//! Hardware ray tracing and MetalFX denoise/upscale, driven by raw Objective-C messages on miniquad's Metal device.

use core::arch::aarch64::{float32x4_t, vld1q_f32};
use macroquad::prelude::*;
use objc::runtime::{Object, BOOL, NO, YES};
use objc::{class, msg_send, sel, sel_impl};

type Id = *mut Object;

#[link(name = "MetalFX", kind = "framework")]
extern "C" {}

const RGBA16F: u64 = 115;
const DEPTH32F: u64 = 252;
const PRIVATE: u64 = 2 << 4;
const SHARED: u64 = 0;

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Sizes {
    accel: usize,
    build_scratch: usize,
    refit_scratch: usize,
}

#[repr(C)]
struct MtlSize {
    w: usize,
    h: usize,
    d: usize,
}

/// `simd_float4x4`, an aggregate of four vectors, so the ABI passes it in SIMD registers.
#[repr(C)]
#[derive(Clone, Copy)]
struct SimdMat([float32x4_t; 4]);

fn simd(m: Mat4) -> SimdMat {
    let a = m.to_cols_array();
    unsafe { SimdMat([vld1q_f32(a[0..].as_ptr()), vld1q_f32(a[4..].as_ptr()), vld1q_f32(a[8..].as_ptr()), vld1q_f32(a[12..].as_ptr())]) }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Instance {
    transform: [f32; 12],
    options: u32,
    mask: u32,
    ift_offset: u32,
    as_index: u32,
}

/// `alb.w == 0` means look up the ground texture.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Tri {
    pub alb: [f32; 4],
    pub n: [f32; 4],
}

unsafe fn nsstring(s: &str) -> Id {
    let ns: Id = msg_send![class!(NSString), alloc];
    msg_send![ns, initWithBytes: s.as_ptr() length: s.len() encoding: 4usize]
}

unsafe fn nsstring_to_string(ns: Id) -> String {
    if ns.is_null() {
        return String::new();
    }
    let p: *const std::os::raw::c_char = msg_send![ns, UTF8String];
    std::ffi::CStr::from_ptr(p).to_string_lossy().into_owned()
}

unsafe fn buffer(device: Id, data: *const u8, len: usize) -> Id {
    msg_send![device, newBufferWithBytes: data length: len.max(16) options: SHARED]
}

unsafe fn blas_desc(vbuf: Id, ibuf: Id, tris: usize) -> Id {
    let g: Id = msg_send![class!(MTLAccelerationStructureTriangleGeometryDescriptor), descriptor];
    let _: () = msg_send![g, setVertexBuffer: vbuf];
    let _: () = msg_send![g, setVertexStride: 12usize];
    let _: () = msg_send![g, setIndexBuffer: ibuf];
    let _: () = msg_send![g, setIndexType: 1usize];
    let _: () = msg_send![g, setTriangleCount: tris];
    let _: () = msg_send![g, setOpaque: YES];
    let d: Id = msg_send![class!(MTLPrimitiveAccelerationStructureDescriptor), descriptor];
    let arr: Id = msg_send![class!(NSArray), arrayWithObject: g];
    let _: () = msg_send![d, setGeometryDescriptors: arr];
    d
}

pub struct Rt {
    device: Id,
    pso: Id,
    compose: Id,
    static_blas: Id,
    static_tri: Id,
    air_blas: Id,
    air_cap: usize,
    air_vbuf: Id,
    air_ibuf: Id,
    air_tri: Id,
    air_vcap: usize,
    tlas: Id,
    inst_buf: Id,
    scratch: Id,
    scratch_cap: usize,
    scaler: Id,
    denoised: bool,
    pub frame: u32,
    sizes: (u32, u32, u32, u32),
    pub use_denoiser: bool,
}

impl Rt {
    pub fn new(device: *mut std::ffi::c_void, queue: *mut std::ffi::c_void, src: &str, pos: &[[f32; 3]], idx: &[u32], tris: &[Tri]) -> Option<Rt> {
        unsafe {
            let device = device as Id;
            let queue = queue as Id;
            let ok: BOOL = msg_send![device, supportsRaytracing];
            if ok == NO {
                eprintln!("rt: device has no ray tracing support");
                return None;
            }
            let mut err: Id = std::ptr::null_mut();
            let lib: Id = msg_send![device, newLibraryWithSource: nsstring(src) options: std::ptr::null_mut::<Object>() error: &mut err];
            if lib.is_null() {
                let d: Id = msg_send![err, localizedDescription];
                panic!("rt shader: {}", nsstring_to_string(d));
            }
            let f: Id = msg_send![lib, newFunctionWithName: nsstring("trace")];
            let pso: Id = msg_send![device, newComputePipelineStateWithFunction: f error: &mut err];
            assert!(!pso.is_null(), "rt pipeline");
            let f2: Id = msg_send![lib, newFunctionWithName: nsstring("compose")];
            let compose: Id = msg_send![device, newComputePipelineStateWithFunction: f2 error: &mut err];
            assert!(!compose.is_null(), "rt compose pipeline");
            let vbuf = buffer(device, pos.as_ptr() as *const u8, std::mem::size_of_val(pos));
            let ibuf = buffer(device, idx.as_ptr() as *const u8, std::mem::size_of_val(idx));
            let static_tri = buffer(device, tris.as_ptr() as *const u8, std::mem::size_of_val(tris));
            let desc = blas_desc(vbuf, ibuf, idx.len() / 3);
            let sizes: Sizes = msg_send![device, accelerationStructureSizesWithDescriptor: desc];
            let static_blas: Id = msg_send![device, newAccelerationStructureWithSize: sizes.accel];
            let scratch: Id = msg_send![device, newBufferWithLength: sizes.build_scratch options: PRIVATE];
            let cb: Id = msg_send![queue, commandBuffer];
            let enc: Id = msg_send![cb, accelerationStructureCommandEncoder];
            let _: () = msg_send![enc, buildAccelerationStructure: static_blas descriptor: desc scratchBuffer: scratch scratchBufferOffset: 0usize];
            let _: () = msg_send![enc, endEncoding];
            let _: () = msg_send![cb, commit];
            let _: () = msg_send![cb, waitUntilCompleted];
            eprintln!("rt: static BLAS {} triangles, {:.1} MB", idx.len() / 3, sizes.accel as f64 / 1e6);
            let inst_buf: Id = msg_send![device, newBufferWithLength: 2 * std::mem::size_of::<Instance>() options: SHARED];
            Some(Rt {
                device,
                pso,
                compose,
                static_blas,
                static_tri,
                air_blas: std::ptr::null_mut(),
                air_cap: 0,
                air_vbuf: std::ptr::null_mut(),
                air_ibuf: std::ptr::null_mut(),
                air_tri: std::ptr::null_mut(),
                air_vcap: 0,
                tlas: std::ptr::null_mut(),
                inst_buf,
                scratch,
                scratch_cap: sizes.build_scratch,
                scaler: std::ptr::null_mut(),
                denoised: false,
                frame: 0,
                sizes: (0, 0, 0, 0),
                use_denoiser: false,
            })
        }
    }

    unsafe fn ensure_scratch(&mut self, n: usize) {
        if n > self.scratch_cap {
            self.scratch = msg_send![self.device, newBufferWithLength: n options: PRIVATE];
            self.scratch_cap = n;
        }
    }

    pub fn update(&mut self, cb: *mut std::ffi::c_void, pos: &[[f32; 3]], idx: &[u32], tris: &[Tri]) {
        unsafe {
            let cb = cb as Id;
            if pos.len() > self.air_vcap || idx.len() / 3 > self.air_cap {
                self.air_vcap = pos.len().max(1) * 2;
                self.air_cap = (idx.len() / 3).max(1) * 2;
                self.air_vbuf = msg_send![self.device, newBufferWithLength: self.air_vcap * 12 options: SHARED];
                self.air_ibuf = msg_send![self.device, newBufferWithLength: self.air_cap * 12 options: SHARED];
                self.air_tri = msg_send![self.device, newBufferWithLength: self.air_cap * std::mem::size_of::<Tri>() options: SHARED];
                self.air_blas = std::ptr::null_mut();
            }
            let cp = |b: Id, data: *const u8, len: usize| {
                let dst: *mut u8 = msg_send![b, contents];
                std::ptr::copy_nonoverlapping(data, dst, len);
            };
            cp(self.air_vbuf, pos.as_ptr() as *const u8, std::mem::size_of_val(pos));
            cp(self.air_ibuf, idx.as_ptr() as *const u8, std::mem::size_of_val(idx));
            cp(self.air_tri, tris.as_ptr() as *const u8, std::mem::size_of_val(tris));
            let desc = blas_desc(self.air_vbuf, self.air_ibuf, idx.len() / 3);
            let sizes: Sizes = msg_send![self.device, accelerationStructureSizesWithDescriptor: desc];
            if self.air_blas.is_null() || {
                let s: usize = msg_send![self.air_blas, size];
                s < sizes.accel
            } {
                self.air_blas = msg_send![self.device, newAccelerationStructureWithSize: sizes.accel * 2];
            }
            let id = [1.0f32, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0];
            let inst = [
                Instance { transform: id, options: 4, mask: 0xFF, ift_offset: 0, as_index: 0 },
                Instance { transform: id, options: 4, mask: 0xFF, ift_offset: 0, as_index: 1 },
            ];
            cp(self.inst_buf, inst.as_ptr() as *const u8, std::mem::size_of_val(&inst));
            let td: Id = msg_send![class!(MTLInstanceAccelerationStructureDescriptor), descriptor];
            let list = [self.static_blas, self.air_blas];
            let arr: Id = msg_send![class!(NSArray), arrayWithObjects: list.as_ptr() count: 2usize];
            let _: () = msg_send![td, setInstancedAccelerationStructures: arr];
            let _: () = msg_send![td, setInstanceCount: 2usize];
            let _: () = msg_send![td, setInstanceDescriptorBuffer: self.inst_buf];
            let tsizes: Sizes = msg_send![self.device, accelerationStructureSizesWithDescriptor: td];
            if self.tlas.is_null() {
                self.tlas = msg_send![self.device, newAccelerationStructureWithSize: tsizes.accel * 2];
            }
            self.ensure_scratch(sizes.build_scratch.max(tsizes.build_scratch) * 2);
            let enc: Id = msg_send![cb, accelerationStructureCommandEncoder];
            let _: () = msg_send![enc, buildAccelerationStructure: self.air_blas descriptor: desc scratchBuffer: self.scratch scratchBufferOffset: 0usize];
            let _: () = msg_send![enc, endEncoding];
            let enc: Id = msg_send![cb, accelerationStructureCommandEncoder];
            let _: () = msg_send![enc, buildAccelerationStructure: self.tlas descriptor: td scratchBuffer: self.scratch scratchBufferOffset: 0usize];
            let _: () = msg_send![enc, endEncoding];
        }
    }

    pub fn trace(&mut self, cb: *mut std::ffi::c_void, uniforms: &[u8], inputs: &[*mut std::ffi::c_void], outputs: &[*mut std::ffi::c_void], w: u32, h: u32) {
        unsafe {
            let cb = cb as Id;
            let enc: Id = msg_send![cb, computeCommandEncoder];
            let _: () = msg_send![enc, setComputePipelineState: self.pso];
            let _: () = msg_send![enc, setBytes: uniforms.as_ptr() length: uniforms.len() atIndex: 0usize];
            let _: () = msg_send![enc, setAccelerationStructure: self.tlas atBufferIndex: 1usize];
            let _: () = msg_send![enc, setBuffer: self.static_tri offset: 0usize atIndex: 2usize];
            let _: () = msg_send![enc, setBuffer: self.air_tri offset: 0usize atIndex: 3usize];
            let _: () = msg_send![enc, useResource: self.static_blas usage: 1usize];
            let _: () = msg_send![enc, useResource: self.air_blas usage: 1usize];
            for (k, t) in inputs.iter().chain(outputs.iter()).enumerate() {
                let _: () = msg_send![enc, setTexture: *t as Id atIndex: k];
            }
            let grid = MtlSize { w: w as usize, h: h as usize, d: 1 };
            let tg = MtlSize { w: 8, h: 8, d: 1 };
            let _: () = msg_send![enc, dispatchThreads: grid threadsPerThreadgroup: tg];
            let _: () = msg_send![enc, endEncoding];
            self.frame = self.frame.wrapping_add(1);
        }
    }

    /// Joint-bilateral filter of the bounce, reflection and shadow terms, then the final composition.
    pub fn compose(&mut self, cb: *mut std::ffi::c_void, uniforms: &[u8], textures: &[*mut std::ffi::c_void], w: u32, h: u32) {
        unsafe {
            let enc: Id = msg_send![cb as Id, computeCommandEncoder];
            let _: () = msg_send![enc, setComputePipelineState: self.compose];
            let _: () = msg_send![enc, setBytes: uniforms.as_ptr() length: uniforms.len() atIndex: 0usize];
            for (k, t) in textures.iter().enumerate() {
                let _: () = msg_send![enc, setTexture: *t as Id atIndex: k];
            }
            let grid = MtlSize { w: w as usize, h: h as usize, d: 1 };
            let tg = MtlSize { w: 8, h: 8, d: 1 };
            let _: () = msg_send![enc, dispatchThreads: grid threadsPerThreadgroup: tg];
            let _: () = msg_send![enc, endEncoding];
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn upscale(
        &mut self,
        cb: *mut std::ffi::c_void,
        t: &[*mut std::ffi::c_void; 8],
        (iw, ih, ow, oh): (u32, u32, u32, u32),
        jitter: Vec2,
        view: Mat4,
        proj: Mat4,
        reset: bool,
    ) {
        unsafe {
            if self.scaler.is_null() || self.sizes != (iw, ih, ow, oh) || self.denoised != self.use_denoiser {
                self.sizes = (iw, ih, ow, oh);
                let dcls = objc::runtime::Class::get("MTLFXTemporalDenoisedScalerDescriptor");
                let mut sc: Id = std::ptr::null_mut();
                let dcls = if self.use_denoiser { dcls } else { None };
                if let Some(dcls) = dcls {
                    let d: Id = msg_send![dcls, new];
                    let _: () = msg_send![d, setColorTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setDepthTextureFormat: DEPTH32F];
                    let _: () = msg_send![d, setMotionTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setOutputTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setDiffuseAlbedoTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setSpecularAlbedoTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setNormalTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setRoughnessTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setInputWidth: iw as usize];
                    let _: () = msg_send![d, setInputHeight: ih as usize];
                    let _: () = msg_send![d, setOutputWidth: ow as usize];
                    let _: () = msg_send![d, setOutputHeight: oh as usize];
                    sc = msg_send![d, newTemporalDenoisedScalerWithDevice: self.device];
                }
                self.denoised = !sc.is_null();
                if sc.is_null() {
                    let d: Id = msg_send![class!(MTLFXTemporalScalerDescriptor), new];
                    let _: () = msg_send![d, setColorTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setDepthTextureFormat: DEPTH32F];
                    let _: () = msg_send![d, setMotionTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setOutputTextureFormat: RGBA16F];
                    let _: () = msg_send![d, setInputWidth: iw as usize];
                    let _: () = msg_send![d, setInputHeight: ih as usize];
                    let _: () = msg_send![d, setOutputWidth: ow as usize];
                    let _: () = msg_send![d, setOutputHeight: oh as usize];
                    sc = msg_send![d, newTemporalScalerWithDevice: self.device];
                }
                assert!(!sc.is_null(), "MetalFX scaler");
                eprintln!("rt: MetalFX {} {iw}x{ih} -> {ow}x{oh}", if self.denoised { "temporal denoised scaler" } else { "temporal scaler" });
                self.scaler = sc;
            }
            let s = self.scaler;
            let id = |k: usize| t[k] as Id;
            let _: () = msg_send![s, setColorTexture: id(0)];
            let _: () = msg_send![s, setDepthTexture: id(1)];
            let _: () = msg_send![s, setMotionTexture: id(2)];
            let _: () = msg_send![s, setOutputTexture: id(7)];
            let _: () = msg_send![s, setJitterOffsetX: jitter.x];
            let _: () = msg_send![s, setJitterOffsetY: jitter.y];
            let _: () = msg_send![s, setMotionVectorScaleX: iw as f32];
            let _: () = msg_send![s, setMotionVectorScaleY: ih as f32];
            let _: () = msg_send![s, setDepthReversed: YES];
            if self.denoised {
                let _: () = msg_send![s, setDiffuseAlbedoTexture: id(3)];
                let _: () = msg_send![s, setSpecularAlbedoTexture: id(4)];
                let _: () = msg_send![s, setNormalTexture: id(5)];
                let _: () = msg_send![s, setRoughnessTexture: id(6)];
                let _: () = msg_send![s, setWorldToViewMatrix: simd(view)];
                let _: () = msg_send![s, setViewToClipMatrix: simd(proj)];
                let _: () = msg_send![s, setShouldResetHistory: if reset { YES } else { NO }];
            } else {
                let _: () = msg_send![s, setReset: if reset { YES } else { NO }];
            }
            let _: () = msg_send![s, encodeToCommandBuffer: cb as Id];
        }
    }

}

/// Halton(2,3) sub-pixel jitter in pixels, in [-0.5, 0.5].
pub fn jitter(frame: u32) -> Vec2 {
    let h = |mut i: u32, b: u32| {
        let (mut f, mut r) = (1.0f32, 0.0f32);
        while i > 0 {
            f /= b as f32;
            r += f * (i % b) as f32;
            i /= b;
        }
        r
    };
    let i = frame % 16 + 1;
    vec2(h(i, 2) - 0.5, h(i, 3) - 0.5)
}
