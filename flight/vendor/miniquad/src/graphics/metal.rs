#![allow(non_snake_case)]

use crate::native::apple::{
    apple_util::{self, msg_send_},
    frameworks::*,
};

use super::*;

// https://developer.apple.com/metal/Metal-Feature-Set-Tables.pdf
const MAX_UNIFORM_BUFFER_SIZE: u64 = 4 * 1024 * 1024;
const NUM_INFLIGHT_FRAMES: usize = 3;
#[cfg(any(target_os = "macos", all(target_os = "ios", target_arch = "x86_64")))]
const UNIFORM_BUFFER_ALIGN: u64 = 256;
#[cfg(all(target_os = "ios", not(target_arch = "x86_64")))]
const UNIFORM_BUFFER_ALIGN: u64 = 16;

impl From<VertexFormat> for MTLVertexFormat {
    fn from(vf: VertexFormat) -> Self {
        match vf {
            VertexFormat::Float1 => MTLVertexFormat::Float,
            VertexFormat::Float2 => MTLVertexFormat::Float2,
            VertexFormat::Float3 => MTLVertexFormat::Float3,
            VertexFormat::Float4 => MTLVertexFormat::Float4,
            VertexFormat::Byte1 => MTLVertexFormat::UChar,
            VertexFormat::Byte2 => MTLVertexFormat::UChar2,
            VertexFormat::Byte3 => MTLVertexFormat::UChar3,
            VertexFormat::Byte4 => MTLVertexFormat::UChar4,
            VertexFormat::Short1 => MTLVertexFormat::Short,
            VertexFormat::Short2 => MTLVertexFormat::Short2,
            VertexFormat::Short3 => MTLVertexFormat::Short3,
            VertexFormat::Short4 => MTLVertexFormat::Short4,
            VertexFormat::Int1 => MTLVertexFormat::Int,
            VertexFormat::Int2 => MTLVertexFormat::Int2,
            VertexFormat::Int3 => MTLVertexFormat::Int3,
            VertexFormat::Int4 => MTLVertexFormat::Int4,
            VertexFormat::Mat4 => MTLVertexFormat::Float4,
        }
    }
}

impl From<UniformType> for MTLVertexFormat {
    fn from(ut: UniformType) -> Self {
        match ut {
            UniformType::Float1 => MTLVertexFormat::Float,
            UniformType::Float2 => MTLVertexFormat::Float2,
            UniformType::Float3 => MTLVertexFormat::Float3,
            UniformType::Float4 => MTLVertexFormat::Float4,
            UniformType::Int1 => MTLVertexFormat::Int,
            UniformType::Int2 => MTLVertexFormat::Int2,
            UniformType::Int3 => MTLVertexFormat::Int3,
            UniformType::Int4 => MTLVertexFormat::Int4,
            UniformType::Mat4 => MTLVertexFormat::Float4,
        }
    }
}

impl From<Comparison> for MTLCompareFunction {
    fn from(cmp: Comparison) -> Self {
        match cmp {
            Comparison::Never => MTLCompareFunction::Never,
            Comparison::Less => MTLCompareFunction::Less,
            Comparison::LessOrEqual => MTLCompareFunction::LessEqual,
            Comparison::Greater => MTLCompareFunction::Greater,
            Comparison::GreaterOrEqual => MTLCompareFunction::GreaterEqual,
            Comparison::Equal => MTLCompareFunction::Equal,
            Comparison::NotEqual => MTLCompareFunction::NotEqual,
            Comparison::Always => MTLCompareFunction::Always,
        }
    }
}

impl From<BlendFactor> for MTLBlendFactor {
    fn from(factor: BlendFactor) -> Self {
        match factor {
            BlendFactor::Zero => MTLBlendFactor::Zero,
            BlendFactor::One => MTLBlendFactor::One,
            BlendFactor::Value(BlendValue::SourceColor) => MTLBlendFactor::SourceColor,
            BlendFactor::Value(BlendValue::SourceAlpha) => MTLBlendFactor::SourceAlpha,
            BlendFactor::Value(BlendValue::DestinationColor) => MTLBlendFactor::DestinationColor,
            BlendFactor::Value(BlendValue::DestinationAlpha) => MTLBlendFactor::DestinationAlpha,
            BlendFactor::OneMinusValue(BlendValue::SourceColor) => {
                MTLBlendFactor::OneMinusSourceColor
            }
            BlendFactor::OneMinusValue(BlendValue::SourceAlpha) => {
                MTLBlendFactor::OneMinusSourceAlpha
            }
            BlendFactor::OneMinusValue(BlendValue::DestinationColor) => {
                MTLBlendFactor::OneMinusDestinationColor
            }
            BlendFactor::OneMinusValue(BlendValue::DestinationAlpha) => {
                MTLBlendFactor::OneMinusDestinationAlpha
            }
            BlendFactor::SourceAlphaSaturate => MTLBlendFactor::SourceAlphaSaturated,
        }
    }
}

// impl From<StencilOp> for MTLStencilOperation {
//     fn from(op: StencilOp) -> Self {
//         match op {
//             StencilOp::Keep => MTLStencilOperation::Keep,
//             StencilOp::Zero => MTLStencilOperation::Zero,
//             StencilOp::Replace => MTLStencilOperation::Replace,
//             StencilOp::IncrementClamp => MTLStencilOperation::IncrementClamp,
//             StencilOp::DecrementClamp => MTLStencilOperation::DecrementClamp,
//             StencilOp::Invert => MTLStencilOperation::Invert,
//             StencilOp::IncrementWrap => MTLStencilOperation::IncrementWrap,
//             StencilOp::DecrementWrap => MTLStencilOperation::DecrementWrap,
//         }
//     }
// }

impl From<Equation> for MTLBlendOperation {
    fn from(cf: Equation) -> Self {
        match cf {
            Equation::Add => MTLBlendOperation::Add,
            Equation::Subtract => MTLBlendOperation::Subtract,
            Equation::ReverseSubtract => MTLBlendOperation::ReverseSubtract,
        }
    }
}

impl From<CompareFunc> for MTLCompareFunction {
    fn from(cf: CompareFunc) -> Self {
        match cf {
            CompareFunc::Always => MTLCompareFunction::Always,
            CompareFunc::Never => MTLCompareFunction::Never,
            CompareFunc::Less => MTLCompareFunction::Less,
            CompareFunc::Equal => MTLCompareFunction::Equal,
            CompareFunc::LessOrEqual => MTLCompareFunction::LessEqual,
            CompareFunc::Greater => MTLCompareFunction::Greater,
            CompareFunc::NotEqual => MTLCompareFunction::NotEqual,
            CompareFunc::GreaterOrEqual => MTLCompareFunction::GreaterEqual,
        }
    }
}

impl From<VertexStep> for MTLVertexStepFunction {
    fn from(vs: VertexStep) -> Self {
        match vs {
            VertexStep::PerVertex => MTLVertexStepFunction::PerVertex,
            VertexStep::PerInstance => MTLVertexStepFunction::PerInstance,
        }
    }
}

impl From<PrimitiveType> for MTLPrimitiveType {
    fn from(primitive_type: PrimitiveType) -> Self {
        match primitive_type {
            PrimitiveType::Triangles => MTLPrimitiveType::Triangle,
            PrimitiveType::Lines => MTLPrimitiveType::Line,
            PrimitiveType::Points => MTLPrimitiveType::Point,
        }
    }
}

impl From<TextureFormat> for MTLPixelFormat {
    fn from(format: TextureFormat) -> Self {
        match format {
            TextureFormat::RGBA8 => MTLPixelFormat::RGBA8Unorm,
            //TODO: Depth16Unorm ?
            TextureFormat::Depth => MTLPixelFormat::Depth32Float_Stencil8,
            TextureFormat::RGBA16F => MTLPixelFormat::RGBA16Float,
            TextureFormat::Depth32 => MTLPixelFormat::Depth32Float,
            _ => todo!(),
        }
    }
}

// impl From<CullFace> for MTLCullMode {
//     fn from(cull_face: CullFace) -> Self {
//         match cull_face {
//             CullFace::Back => MTLCullMode::Back,
//             CullFace::Front => MTLCullMode::Front,
//             CullFace::Nothing => MTLCullMode::None,
//         }
//     }
// }

// impl From<FrontFaceOrder> for MTLWinding {
//     fn from(order: FrontFaceOrder) -> Self {
//         match order {
//             FrontFaceOrder::Clockwise => MTLWinding::Clockwise,
//             FrontFaceOrder::CounterClockwise => MTLWinding::CounterClockwise,
//         }
//     }
// }

fn params_bpr(f: TextureFormat) -> usize {
    f.size(1, 1) as usize
}

#[inline]
fn roundup_ub_buffer(current_buffer: u64) -> u64 {
    ((current_buffer) + ((UNIFORM_BUFFER_ALIGN) - 1)) & !((UNIFORM_BUFFER_ALIGN) - 1)
}

// this scenario:
// buffer.update(); draw(buffer); buffer.update(); draw(buffer);
// is very problematic with metal's ownership model.
// buffer.update() half-update buffer - it doesn't really send data to the GPU claiming ownership,
// it postpone reading the CPU memory until drawcall will actually happen.
// There is no way to flush the buffer and makes metal's "update" function to update GPU memory right away.
// Thus miniquad keeps a lot of buffer's copies...
const BUFFERS_IN_ROTATION: usize = 30;

#[derive(Clone, Copy, Debug)]
pub struct Buffer {
    raw: [ObjcId; BUFFERS_IN_ROTATION],
    //buffer_type: BufferType,
    size: usize,
    /// Element size in bytes (2 or 4 for index buffers).
    element_size: usize,
    /// Immutable buffers hold one MTLBuffer in every rotation slot.
    shared: bool,
    value: usize,
    next_value: usize,
}

#[derive(Debug)]
struct ShaderInternal {
    vertex_function: ObjcId,
    fragment_function: ObjcId,
    //uniforms: Vec<ShaderUniform>,
    // the distance, in bytes, between two uniforms in uniforms buffer
    //stride: u64,
}

struct RenderPassInternal {
    render_pass_desc: ObjcId,
    texture: Vec<TextureId>,
    _depth_texture: Option<TextureId>,
}

#[derive(Clone, Debug)]
struct PipelineInternal {
    /// MTLRenderPipelineDescriptor kept to build one state per render-target layout.
    descriptor: ObjcId,
    variants: Vec<(PassKey, ObjcId)>,
    color_blend: Option<BlendState>,
    alpha_blend: Option<BlendState>,
    cull: u64,
    winding: u64,
    primitive: PrimitiveType,
    depth_stencil_state: ObjcId,
    //layout: Vec<BufferLayout>,
    //attributes: Vec<VertexAttributeInternal>,
    _shader: ShaderId,
    //params: PipelineParams,
}

#[derive(Clone, Copy)]
struct Texture {
    texture: ObjcId,
    sampler: ObjcId,
    sampler_descriptor: ObjcId,
    params: TextureParams,
}
struct Textures(Vec<Texture>);

impl Textures {
    fn get(&self, texture: TextureId) -> Texture {
        match texture.0 {
            TextureIdInner::Raw(RawId::Metal(_texture)) => unimplemented!(),
            TextureIdInner::Raw(RawId::OpenGl(_)) => panic!("Gl texture in Metal context!"),
            TextureIdInner::Managed(texture) => self.0[texture],
        }
    }

    fn get_mut(&mut self, texture: TextureId) -> &mut Texture {
        match texture.0 {
            TextureIdInner::Raw(RawId::Metal(_texture)) => unimplemented!(),
            TextureIdInner::Raw(RawId::OpenGl(_)) => panic!("Gl texture in Metal context!"),
            TextureIdInner::Managed(texture) => &mut self.0[texture],
        }
    }
}
/// Attachment layout of the current render pass: a Metal pipeline state is
/// only valid for one combination of colour formats, sample count and
/// depth/stencil formats, so pipelines are built lazily per layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PassKey {
    colors: [u64; 8],
    n: usize,
    samples: u64,
    depth: u64,
    stencil: u64,
}

pub struct MetalContext {
    current_pass_key: Option<PassKey>,
    index_size: usize,
    capture_requested: bool,
    captured: Option<(u32, u32, Vec<u8>)>,
    last_gpu_ms: f64,
    buffers: Vec<Buffer>,
    shaders: Vec<ShaderInternal>,
    pipelines: Vec<PipelineInternal>,
    textures: Textures,
    passes: Vec<RenderPassInternal>,
    command_queue: ObjcId,
    command_buffer: Option<ObjcId>,
    render_encoder: Option<ObjcId>,
    view: ObjcId,
    device: ObjcId,
    current_frame_index: usize,
    uniform_buffers: [ObjcId; 3],
    // cached index_buffer from apply_bindings
    index_buffer: Option<ObjcId>,
    // cached pipeline from apply_pipeline
    current_pipeline: Option<Pipeline>,
    current_ub_offset: u64,
}

impl Default for MetalContext {
    fn default() -> Self {
        Self::new()
    }
}

impl MetalContext {
    pub fn new() -> MetalContext {
        unsafe {
            let view = crate::window::apple_view();
            assert!(!view.is_null());
            let device: ObjcId = msg_send![view, device];
            assert!(!device.is_null());
            let command_queue: ObjcId = msg_send![device, newCommandQueue];

            if false {
                let capture_manager = msg_send_![class![MTLCaptureManager], sharedCaptureManager];
                assert!(!capture_manager.is_null());

                let MTLCaptureDestinationGPUTraceDocument = 2u64;
                if !msg_send![
                    capture_manager,
                    supportsDestination: MTLCaptureDestinationGPUTraceDocument
                ] {
                    // put this into Info.plist near the binary (in target/debug/whatever/whatever, not in the working directory)
                    /*
                    <?xml version="1.0" encoding="UTF-8"?>
                    <!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
                    <plist version="1.0">
                    <dict>
                        <key>MetalCaptureEnabled</key>
                        <true/>
                    </dict>
                    </plist>
                    */
                    panic!("capture failed (probably missing Info.plist, read the comment near this panic)");
                }

                let capture_descriptor =
                    msg_send_![msg_send_![class![MTLCaptureDescriptor], alloc], init];
                msg_send_![capture_descriptor, setCaptureObject: device];
                msg_send_![
                    capture_descriptor,
                    setDestination: MTLCaptureDestinationGPUTraceDocument
                ];
                let path = apple_util::str_to_nsstring("/Users/fedor/wtf1.gputrace");
                let url = msg_send_![class!(NSURL), fileURLWithPath: path];
                msg_send_![capture_descriptor, setOutputURL: url];

                let mut error: ObjcId = nil;
                if !msg_send![capture_manager, startCaptureWithDescriptor:capture_descriptor
                              error:&mut error]
                {
                    let description: ObjcId = msg_send![error, localizedDescription];
                    let string = apple_util::nsstring_to_string(description);
                    panic!("Capture error: {}", string);
                }
            }

            #[cfg(target_os = "macos")]
            let options = {
                MTLResourceOptions::CPUCacheModeWriteCombined
                    | MTLResourceOptions::StorageModeManaged
            };
            #[cfg(target_os = "ios")]
            let options = { MTLResourceOptions::CPUCacheModeWriteCombined };

            let uniform_buffers = [
                msg_send![device, newBufferWithLength:MAX_UNIFORM_BUFFER_SIZE
                          options:options],
                msg_send![device, newBufferWithLength:MAX_UNIFORM_BUFFER_SIZE
                          options:options],
                msg_send![device, newBufferWithLength:MAX_UNIFORM_BUFFER_SIZE
                          options:options],
            ];

            MetalContext {
                current_pass_key: None,
                index_size: 2,
                capture_requested: false,
                captured: None,
                last_gpu_ms: 0.0,
                command_queue,
                command_buffer: None,
                render_encoder: None,
                view,
                device,
                buffers: vec![],
                shaders: vec![],
                pipelines: vec![],
                textures: Textures(Vec::new()),
                passes: vec![],
                index_buffer: None,
                current_pipeline: None,
                uniform_buffers,
                current_frame_index: 1,
                current_ub_offset: 0,
            }
        }
    }
}

unsafe fn build_pipeline_variant(device: ObjcId, pipeline: &PipelineInternal, key: &PassKey) -> ObjcId {
    let descriptor = pipeline.descriptor;
    let color_attachments = msg_send_![descriptor, colorAttachments];
    for i in 0..8usize {
        let color_attachment = msg_send_![color_attachments, objectAtIndexedSubscript: i];
        let fmt = if i < key.n { key.colors[i] } else { 0 };
        msg_send_![color_attachment, setPixelFormat: fmt];
        let blend = if i < key.n { pipeline.color_blend } else { None };
        msg_send_![color_attachment, setBlendingEnabled: BOOL::from(blend.is_some())];
        if let Some(color_blend) = blend {
            let alpha_blend = pipeline.alpha_blend.unwrap_or(color_blend);
            let BlendState { equation: eq_rgb, sfactor: src_rgb, dfactor: dst_rgb } = color_blend;
            let BlendState { equation: eq_alpha, sfactor: src_alpha, dfactor: dst_alpha } = alpha_blend;
            msg_send_![color_attachment, setRgbBlendOperation: MTLBlendOperation::from(eq_rgb)];
            msg_send_![color_attachment, setAlphaBlendOperation: MTLBlendOperation::from(eq_alpha)];
            msg_send_![color_attachment, setSourceRGBBlendFactor: MTLBlendFactor::from(src_rgb)];
            msg_send_![color_attachment, setSourceAlphaBlendFactor: MTLBlendFactor::from(src_alpha)];
            msg_send_![color_attachment, setDestinationRGBBlendFactor: MTLBlendFactor::from(dst_rgb)];
            msg_send_![color_attachment, setDestinationAlphaBlendFactor: MTLBlendFactor::from(dst_alpha)];
        }
    }
    msg_send_![descriptor, setRasterSampleCount: key.samples];
    msg_send_![descriptor, setDepthAttachmentPixelFormat: key.depth];
    msg_send_![descriptor, setStencilAttachmentPixelFormat: key.stencil];

    let mut error: ObjcId = nil;
    let pipeline_state: ObjcId = msg_send![
        device,
        newRenderPipelineStateWithDescriptor: descriptor
        error: &mut error
    ];
    if pipeline_state.is_null() {
        let description: ObjcId = msg_send![error, localizedDescription];
        let string = apple_util::nsstring_to_string(description);
        panic!("newRenderPipelineStateWithDescriptor error: {}", string);
    }
    pipeline_state
}

/// Metal-only extensions used by applications that need more than the
/// portable API: MSAA depth resolve, frame capture, GPU timing and raw
/// handles for interop (compute, ray tracing, MetalFX).
impl MetalContext {
    /// Resolve the pass's multisampled depth into `tex` (sample 0).
    pub fn set_depth_resolve(&mut self, pass: RenderPass, tex: TextureId) {
        unsafe {
            let desc = self.passes[pass.0].render_pass_desc;
            let depth_attachment = msg_send_![desc, depthAttachment];
            let t = self.textures.get(tex).texture;
            msg_send_![depth_attachment, setResolveTexture: t];
            msg_send_![depth_attachment, setStoreAction: MTLStoreAction::MultisampleResolve];
            msg_send_![depth_attachment, setDepthResolveFilter: 0u64];
        }
    }
    /// Copy the drawable at the end of the next frame (needs
    /// `MINIQUAD_METAL_CAPTURE=1` at window creation).
    pub fn request_capture(&mut self) {
        self.capture_requested = true;
    }
    /// RGBA8 pixels of the last captured frame, top row first.
    pub fn take_capture(&mut self) -> Option<(u32, u32, Vec<u8>)> {
        self.captured.take()
    }
    /// GPU time of the last committed frame, in milliseconds.
    pub fn last_gpu_ms(&self) -> f64 {
        self.last_gpu_ms
    }
    pub fn raw_device(&self) -> *mut std::ffi::c_void {
        self.device as _
    }
    pub fn raw_command_queue(&self) -> *mut std::ffi::c_void {
        self.command_queue as _
    }
    /// The frame's command buffer, for encoding compute/blit work between
    /// render passes. Must not be called inside a pass.
    pub fn raw_command_buffer(&mut self) -> *mut std::ffi::c_void {
        assert!(self.render_encoder.is_none(), "raw_command_buffer inside a render pass");
        if self.command_buffer.is_none() {
            self.command_buffer = Some(unsafe { msg_send![self.command_queue, commandBuffer] });
        }
        self.command_buffer.unwrap() as _
    }
    pub fn raw_texture(&self, tex: TextureId) -> *mut std::ffi::c_void {
        self.textures.get(tex).texture as _
    }
    pub fn raw_buffer(&self, buf: BufferId) -> *mut std::ffi::c_void {
        let b = &self.buffers[buf.0];
        b.raw[b.value] as _
    }
}

impl RenderingBackend for MetalContext {
    fn info(&self) -> ContextInfo {
        ContextInfo {
            backend: Backend::Metal,
            gl_version_string: Default::default(),
            glsl_support: Default::default(),
            features: Features {
                instancing: true,
                resolve_attachments: true,
            },
        }
    }
    fn buffer_size(&mut self, buffer: BufferId) -> usize {
        let buffer = &self.buffers[buffer.0];
        buffer.size
    }
    fn delete_buffer(&mut self, buffer: BufferId) {
        let buffer = &self.buffers[buffer.0];
        unsafe {
            let n = if buffer.shared { 1 } else { BUFFERS_IN_ROTATION };
            for buffer in &buffer.raw[..n] {
                msg_send_![*buffer, release];
            }
        }
    }
    fn delete_texture(&mut self, texture: TextureId) {
        let texture = self.textures.get(texture);
        unsafe {
            msg_send_![texture.texture, release];
        }
    }
    fn apply_viewport(&mut self, _x: i32, _y: i32, _w: i32, _h: i32) {}
    fn apply_scissor_rect(&mut self, x: i32, y: i32, w: i32, h: i32) {
        assert!(self.render_encoder.is_some());

        let (_, screen_height) = crate::window::screen_size();
        let r = MTLScissorRect {
            x: x as _,
            y: (screen_height as i32 - (y + h)) as u64,
            width: w as _,
            height: h as _,
        };
        unsafe { msg_send_![self.render_encoder.unwrap(), setScissorRect: r] };
    }
    fn texture_set_min_filter(
        &mut self,
        texture: TextureId,
        filter: FilterMode,
        mipmap_filter: MipmapFilterMode,
    ) {
        let texture = self.textures.get_mut(texture);

        let filter = match filter {
            FilterMode::Nearest => MTLSamplerMinMagFilter::Nearest,
            FilterMode::Linear => MTLSamplerMinMagFilter::Linear,
        };

        let mipmap_filter = match mipmap_filter {
            MipmapFilterMode::None => MTLSamplerMipFilter::NotMipmapped,
            MipmapFilterMode::Nearest => MTLSamplerMipFilter::Nearest,
            MipmapFilterMode::Linear => MTLSamplerMipFilter::Linear,
        };

        texture.sampler = unsafe {
            let sampler_descriptor = msg_send_![class!(MTLSamplerDescriptor), new];
            msg_send_![sampler_descriptor, setMinFilter: filter];
            msg_send_![sampler_descriptor, setMipFilter: mipmap_filter];
            msg_send_![
                self.device,
                newSamplerStateWithDescriptor: sampler_descriptor
            ]
        };
    }
    fn texture_set_mag_filter(&mut self, texture: TextureId, filter: FilterMode) {
        let texture = self.textures.get_mut(texture);

        let filter = match filter {
            FilterMode::Nearest => MTLSamplerMinMagFilter::Nearest,
            FilterMode::Linear => MTLSamplerMinMagFilter::Linear,
        };

        texture.sampler = unsafe {
            msg_send_![texture.sampler_descriptor, setMagFilter: filter];
            msg_send_![self.device, newSamplerStateWithDescriptor: texture.sampler_descriptor]
        };
    }
    fn texture_set_wrap(&mut self, texture: TextureId, wrap_x: TextureWrap, wrap_y: TextureWrap) {
        let texture = self.textures.get_mut(texture);

        let wrap_s = match wrap_x {
            TextureWrap::Repeat => MTLSamplerAddressMode::Repeat,
            TextureWrap::Mirror => MTLSamplerAddressMode::MirrorRepeat,
            TextureWrap::Clamp => MTLSamplerAddressMode::ClampToEdge,
        };

        let wrap_t = match wrap_y {
            TextureWrap::Repeat => MTLSamplerAddressMode::Repeat,
            TextureWrap::Mirror => MTLSamplerAddressMode::MirrorRepeat,
            TextureWrap::Clamp => MTLSamplerAddressMode::ClampToEdge,
        };

        texture.sampler = unsafe {
            //msg_send_![texture.sampler_descriptor, setRAddressMode: wrap];
            msg_send_![texture.sampler_descriptor, setSAddressMode: wrap_s];
            msg_send_![texture.sampler_descriptor, setTAddressMode: wrap_t];
            msg_send_![self.device, newSamplerStateWithDescriptor: texture.sampler_descriptor]
        };
    }
    fn texture_resize(
        &mut self,
        _texture: TextureId,
        _width: u32,
        _height: u32,
        _bytes: Option<&[u8]>,
    ) {
        unimplemented!()
    }
    fn texture_read_pixels(&mut self, _texture: TextureId, _bytes: &mut [u8]) {
        unimplemented!()
    }
    fn texture_generate_mipmaps(&mut self, texture: TextureId) {
        unsafe {
            if self.command_buffer.is_none() {
                self.command_buffer = Some(msg_send![self.command_queue, commandBuffer]);
            }
            let command_buffer = self.command_buffer.unwrap();
            let encoder = msg_send_![command_buffer, blitCommandEncoder];
            let texture = self.textures.get(texture);
            msg_send_![encoder, generateMipmapsForTexture: texture.texture];
            msg_send_![encoder, endEncoding];
        }
    }
    fn texture_params(&self, texture: TextureId) -> TextureParams {
        let texture = self.textures.get(texture);
        texture.params
    }
    unsafe fn texture_raw_id(&self, texture: TextureId) -> RawId {
        let texture = self.textures.get(texture);
        RawId::Metal(texture.texture)
    }

    fn clear(
        &mut self,
        color: Option<(f32, f32, f32, f32)>,
        depth: Option<f32>,
        stencil: Option<i32>,
    ) {
        // TODO: begin_pass/end_pass works, but is far from optimal
        self.begin_default_pass(PassAction::Clear {
            color,
            depth,
            stencil,
        });
        self.end_render_pass();
    }

    fn new_render_pass_mrt(
        &mut self,
        color_img: &[TextureId],
        resolve_img: Option<&[TextureId]>,
        depth_img: Option<TextureId>,
    ) -> RenderPass {
        unsafe {
            let render_pass_desc =
                msg_send_![class!(MTLRenderPassDescriptor), renderPassDescriptor];
            msg_send_![render_pass_desc, retain];
            assert!(!render_pass_desc.is_null());
            for (i, color_img) in color_img.iter().enumerate() {
                let color_texture = self.textures.get(*color_img).texture;
                let color_attachment = msg_send_![msg_send_![render_pass_desc, colorAttachments], objectAtIndexedSubscript:i];
                msg_send_![color_attachment, setTexture: color_texture];
                msg_send_![color_attachment, setLoadAction: MTLLoadAction::Clear];
                match resolve_img.and_then(|r| r.get(i)) {
                    Some(resolve) => {
                        let resolve_texture = self.textures.get(*resolve).texture;
                        msg_send_![color_attachment, setResolveTexture: resolve_texture];
                        msg_send_![color_attachment, setStoreAction: MTLStoreAction::MultisampleResolve];
                    }
                    None => {
                        msg_send_![color_attachment, setStoreAction: MTLStoreAction::Store];
                    }
                }
            }
            if let Some(depth_img) = depth_img {
                let depth_texture = self.textures.get(depth_img).texture;

                let depth_attachment = msg_send_![render_pass_desc, depthAttachment];
                msg_send_![depth_attachment, setTexture: depth_texture];
                msg_send_![depth_attachment, setLoadAction: MTLLoadAction::Clear];
                msg_send_![depth_attachment, setStoreAction: MTLStoreAction::Store];
                msg_send_![depth_attachment, setClearDepth:1.];

                if self.textures.get(depth_img).params.format == TextureFormat::Depth {
                    let stencil_attachment = msg_send_![render_pass_desc, stencilAttachment];
                    msg_send_![stencil_attachment, setTexture: depth_texture];
                    msg_send_![stencil_attachment, setStoreAction: MTLStoreAction::DontCare];
                }
            }
            let pass = RenderPassInternal {
                render_pass_desc,
                texture: color_img.to_vec(),
                _depth_texture: depth_img,
            };

            self.passes.push(pass);

            RenderPass(self.passes.len() - 1)
        }
    }

    fn delete_render_pass(&mut self, render_pass: RenderPass) {
        let render_pass = &self.passes[render_pass.0];
        unsafe {
            msg_send_![render_pass.render_pass_desc, release];
        }
    }

    fn render_pass_color_attachments(&self, render_pass: RenderPass) -> &[TextureId] {
        &self.passes[render_pass.0].texture
    }

    fn new_buffer(&mut self, _: BufferType, usage: BufferUsage, data: BufferSource) -> BufferId {
        let mut raw = [nil; BUFFERS_IN_ROTATION];
        let (size, element_size) = match &data {
            BufferSource::Slice(data) => (data.size, data.element_size),
            BufferSource::Empty { size, element_size } => (*size, *element_size),
        };
        let shared = usage == BufferUsage::Immutable && matches!(data, BufferSource::Slice(_));
        #[allow(clippy::needless_range_loop)]
        for i in 0..BUFFERS_IN_ROTATION {
            if shared && i > 0 {
                raw[i] = raw[0];
                continue;
            }
            let buffer: ObjcId = if let BufferSource::Slice(data) = &data {
                debug_assert!(data.is_slice);
                let size = data.size as u64;
                unsafe {
                    msg_send![self.device,
                              newBufferWithBytes:data.ptr
                              length:size
                              options:MTLResourceOptions::StorageModeShared]
                }
            } else {
                #[cfg(target_os = "macos")]
                let options = MTLResourceOptions::CPUCacheModeWriteCombined
                    | MTLResourceOptions::StorageModeManaged;
                #[cfg(target_os = "ios")]
                let options = MTLResourceOptions::CPUCacheModeWriteCombined;
                unsafe {
                    msg_send![self.device,
                              newBufferWithLength:size
                              options:options]
                }
            };

            unsafe {
                msg_send_![buffer, retain];
            }
            raw[i] = buffer;
        }
        let buffer = Buffer {
            raw,
            size,
            element_size,
            shared,
            value: 0,
            next_value: 0,
        };
        self.buffers.push(buffer);
        BufferId(self.buffers.len() - 1)
    }

    fn buffer_update(&mut self, buffer: BufferId, data: BufferSource) {
        let data = match data {
            BufferSource::Slice(data) => data,
            _ => panic!("buffer_update expects BufferSource::slice"),
        };
        let buffer = &mut self.buffers[buffer.0];
        assert!(data.size <= buffer.size);

        unsafe {
            let dest: *mut std::ffi::c_void = msg_send![buffer.raw[buffer.next_value], contents];
            std::ptr::copy(data.ptr, dest, data.size);

            #[cfg(target_os = "macos")]
            msg_send_![buffer.raw[buffer.next_value], didModifyRange:NSRange::new(0, data.size as u64)];
        }
        buffer.value = buffer.next_value;
        assert!(!buffer.shared, "buffer_update on an immutable buffer");
    }

    fn new_shader(
        &mut self,
        shader: ShaderSource,
        _meta: ShaderMeta,
    ) -> Result<ShaderId, ShaderError> {
        unsafe {
            let program = match shader {
                ShaderSource::Msl { program } => program,
                _ => panic!("OpenGl source on Metal context"),
            };
            let shader = apple_util::str_to_nsstring(program);
            let mut error: ObjcId = nil;
            let library: ObjcId = msg_send![
                self.device,
                newLibraryWithSource: shader
                options:nil
                error: &mut error
            ];
            if library.is_null() {
                let description: ObjcId = msg_send![error, localizedDescription];
                let string = apple_util::nsstring_to_string(description);
                panic!("Shader {}", string);
            }

            let vertex_function: ObjcId = msg_send![library, newFunctionWithName: apple_util::str_to_nsstring("vertexShader")];
            assert!(!vertex_function.is_null());
            let fragment_function: ObjcId = msg_send![library, newFunctionWithName: apple_util::str_to_nsstring("fragmentShader")];
            assert!(!fragment_function.is_null());
            let shader = ShaderInternal {
                vertex_function,
                fragment_function,
            };
            self.shaders.push(shader);
            Ok(ShaderId(self.shaders.len() - 1))
        }
    }

    fn new_texture(
        &mut self,
        access: TextureAccess,
        bytes: TextureSource,
        params: TextureParams,
    ) -> TextureId {
        let descriptor = unsafe {
            msg_send_![class!(MTLTextureDescriptor),
                       texture2DDescriptorWithPixelFormat:MTLPixelFormat::from(params.format)
                       width: params.width as u64
                       height: params.height as u64
                       mipmapped: params.allocate_mipmaps as BOOL]
        };

        // unsafe {
        //     msg_send_![descriptor, retain];
        // }
        unsafe {
            msg_send_![descriptor, setCpuCacheMode: MTLCPUCacheMode::DefaultCache];

            if access == TextureAccess::RenderTarget {
                if params.format != TextureFormat::Depth {
                    let pixel_format: MTLPixelFormat = params.format.into();
                    msg_send_![descriptor, setPixelFormat: pixel_format];
                }
                msg_send_![descriptor, setStorageMode: MTLStorageMode::Private];
                msg_send_![
                    descriptor,
                    setUsage: MTLTextureUsage::RenderTarget as u64
                        | MTLTextureUsage::ShaderRead as u64
                        | MTLTextureUsage::ShaderWrite as u64
                ];
                if params.sample_count > 1 {
                    msg_send_![descriptor, setTextureType: MTLTextureType::D2Multisample];
                    msg_send_![descriptor, setSampleCount: params.sample_count as u64];
                    msg_send_![descriptor, setMipmapLevelCount: 1u64];
                }
            } else {
                #[cfg(target_os = "macos")]
                {
                    msg_send_![descriptor, setUsage: MTLTextureUsage::ShaderRead];
                    msg_send_![descriptor, setStorageMode: MTLStorageMode::Managed];
                    msg_send_![
                        descriptor,
                        setResourceOptions: MTLResourceOptions::StorageModeManaged
                    ];
                }
                #[cfg(target_os = "ios")]
                {
                    msg_send_![descriptor, setStorageMode: MTLStorageMode::Shared];
                    msg_send_![
                        descriptor,
                        setResourceOptions: MTLResourceOptions::StorageModeShared
                    ];
                }
            }
        };

        match params.kind {
            TextureKind::Texture2D => {
                // on metal textureType2D is the default, nothing to do here
            }
            TextureKind::CubeMap => unsafe {
                msg_send_![descriptor, setTextureType: MTLTextureType::CubeArray];
            },
        }

        let texture = unsafe {
            let sampler_descriptor = msg_send_![class!(MTLSamplerDescriptor), new];
            msg_send_![sampler_descriptor, retain];
            let min_filter = match params.min_filter {
                FilterMode::Nearest => MTLSamplerMinMagFilter::Nearest,
                FilterMode::Linear => MTLSamplerMinMagFilter::Linear,
            };

            let mag_filter = match params.mag_filter {
                FilterMode::Nearest => MTLSamplerMinMagFilter::Nearest,
                FilterMode::Linear => MTLSamplerMinMagFilter::Linear,
            };

            let mipmap_filter = match params.mipmap_filter {
                MipmapFilterMode::None => MTLSamplerMipFilter::NotMipmapped,
                MipmapFilterMode::Nearest => MTLSamplerMipFilter::Nearest,
                MipmapFilterMode::Linear => MTLSamplerMipFilter::Linear,
            };
            msg_send_![sampler_descriptor, setMinFilter: min_filter];
            msg_send_![sampler_descriptor, setMagFilter: mag_filter];
            msg_send_![sampler_descriptor, setMipFilter: mipmap_filter];
            let wrap = match params.wrap {
                TextureWrap::Repeat => MTLSamplerAddressMode::Repeat,
                TextureWrap::Mirror => MTLSamplerAddressMode::MirrorRepeat,
                TextureWrap::Clamp => MTLSamplerAddressMode::ClampToEdge,
            };
            msg_send_![sampler_descriptor, setSAddressMode: wrap];
            msg_send_![sampler_descriptor, setTAddressMode: wrap];
            if params.mipmap_filter != MipmapFilterMode::None && params.min_filter == FilterMode::Linear {
                msg_send_![sampler_descriptor, setMaxAnisotropy: 8u64];
            }

            let sampler_state = msg_send_![
                self.device,
                newSamplerStateWithDescriptor: sampler_descriptor
            ];
            let raw_texture = msg_send_![self.device, newTextureWithDescriptor: descriptor];
            msg_send_![raw_texture, retain];
            self.textures.0.push(Texture {
                sampler: sampler_state,
                texture: raw_texture,
                sampler_descriptor,
                params,
            });
            TextureId(TextureIdInner::Managed(self.textures.0.len() - 1))
        };

        match bytes {
            TextureSource::Empty => {}
            TextureSource::Bytes(bytes) => {
                assert_eq!(
                    params.format.size(params.width, params.height) as usize,
                    bytes.len()
                );

                self.texture_update_part(
                    texture,
                    0,
                    0,
                    params.width as _,
                    params.height as _,
                    bytes,
                );
            }
            TextureSource::Array(array) => {
                for (n, face) in array.iter().enumerate() {
                    for (mipmap_level, bytes) in face.iter().enumerate() {
                        let raw_texture = self.textures.get(texture).texture;
                        let region = MTLRegion {
                            origin: MTLOrigin {
                                x: 0_u64,
                                y: 0_u64,
                                z: 0,
                            },
                            size: MTLSize {
                                width: params.width as u64,
                                height: params.height as u64,
                                depth: 1,
                            },
                        };
                        assert!(bytes.len() as u32 == params.width * params.height * 4);
                        unsafe {
                            msg_send_![raw_texture, replaceRegion:region
                                  mipmapLevel:mipmap_level
                                  slice: n
                                  withBytes:bytes.as_ptr()
                                  bytesPerRow:(params.width * 4) as u64
                                  bytesPerImage:0
                            ];
                        }
                    }
                }
            }
        }
        texture
    }

    fn texture_update_part(
        &mut self,
        texture: TextureId,
        x_offset: i32,
        y_offset: i32,
        width: i32,
        height: i32,
        bytes: &[u8],
    ) {
        let raw_texture = self.textures.get(texture).texture;
        let region = MTLRegion {
            origin: MTLOrigin {
                x: x_offset as u64,
                y: y_offset as u64,
                z: 0,
            },
            size: MTLSize {
                width: width as u64,
                height: height as u64,
                depth: 1,
            },
        };
        unsafe {
            msg_send_![raw_texture, replaceRegion:region
                       mipmapLevel:0
                       withBytes:bytes.as_ptr()
                       bytesPerRow:(params_bpr(self.textures.get(texture).params.format) * width as usize) as u64];
        }
    }

    fn new_pipeline(
        &mut self,
        buffer_layout: &[BufferLayout],
        attributes: &[VertexAttribute],
        shader: ShaderId,
        params: PipelineParams,
    ) -> Pipeline {
        unsafe {
            let shader_internal = &self.shaders[shader.0];

            let vertex_descriptor: ObjcId =
                msg_send![class!(MTLVertexDescriptor), vertexDescriptor];

            let attribute = |i, buffer_index, offset, format: MTLVertexFormat| {
                let mtl_attribute_desc = msg_send_![
                    msg_send_![vertex_descriptor, attributes],
                    objectAtIndexedSubscript: i
                ];
                msg_send_![mtl_attribute_desc, setBufferIndex: buffer_index];
                msg_send_![mtl_attribute_desc, setOffset: offset];
                msg_send_![mtl_attribute_desc, setFormat: format];
            };
            let layout = |i, step_func: VertexStep, stride, step_rate| {
                let mtl_buffer_desc = msg_send_![
                    msg_send_![vertex_descriptor, layouts],
                    objectAtIndexedSubscript: i
                ];
                let step_func: MTLVertexStepFunction = step_func.into();
                msg_send_![mtl_buffer_desc, setStride: stride];
                msg_send_![mtl_buffer_desc, setStepFunction: step_func];
                msg_send_![mtl_buffer_desc, setStepRate: step_rate];
            };

            let mut offsets = [0u64; 50];
            for (i, a) in attributes.iter().enumerate() {
                let offset = &mut offsets[a.buffer_index];
                attribute(
                    i as u64,
                    a.buffer_index as u64 + 1,
                    *offset,
                    a.format.into(),
                );
                *offset += a.format.size_bytes() as u64;
            }
            for (i, buffer) in buffer_layout.iter().enumerate() {
                layout(
                    i as u64 + 1,
                    buffer.step_func,
                    if buffer.stride == 0 {
                        offsets[i]
                    } else {
                        buffer.stride as u64
                    },
                    buffer.step_rate as u64,
                );
            }

            let descriptor = msg_send_![class!(MTLRenderPipelineDescriptor), new];
            msg_send_![descriptor, setVertexFunction:shader_internal.vertex_function];
            msg_send_![descriptor, setFragmentFunction:shader_internal.fragment_function];
            msg_send_![descriptor, setVertexDescriptor: vertex_descriptor];

            let depth_stencil_desc = msg_send_![class!(MTLDepthStencilDescriptor), new];
            msg_send_![depth_stencil_desc, setDepthWriteEnabled: BOOL::from(params.depth_write)];
            msg_send_![depth_stencil_desc, setDepthCompareFunction: MTLCompareFunction::from(params.depth_test)];

            // if let Some(stencil_test) = params.stencil_test {
            //     let back_face_stencil_desc = StencilDescriptor::new();
            //     back_face_stencil_desc.set_stencil_compare_function(stencil_test.back.test_func.into());
            //     back_face_stencil_desc.set_stencil_failure_operation(stencil_test.back.fail_op.into());
            //     back_face_stencil_desc
            //         .set_depth_failure_operation(stencil_test.back.depth_fail_op.into());
            //     back_face_stencil_desc.set_read_mask(stencil_test.back.test_mask);
            //     back_face_stencil_desc.set_write_mask(stencil_test.back.write_mask);

            //     depth_stencil_desc.set_back_face_stencil(Some(back_face_stencil_desc.as_ref()));

            //     let front_face_stencil_desc = StencilDescriptor::new();
            //     front_face_stencil_desc
            //         .set_stencil_compare_function(stencil_test.front.test_func.into());
            //     front_face_stencil_desc
            //         .set_stencil_failure_operation(stencil_test.front.fail_op.into());
            //     front_face_stencil_desc
            //         .set_depth_failure_operation(stencil_test.front.depth_fail_op.into());
            //     front_face_stencil_desc.set_read_mask(stencil_test.front.test_mask);
            //     front_face_stencil_desc.set_write_mask(stencil_test.front.write_mask);

            //     depth_stencil_desc.set_front_face_stencil(Some(front_face_stencil_desc.as_ref()))
            // }

            let depth_stencil_state = msg_send_![
                self.device,
                newDepthStencilStateWithDescriptor: depth_stencil_desc
            ];

            let pipeline = PipelineInternal {
                descriptor,
                variants: vec![],
                color_blend: params.color_blend,
                alpha_blend: params.alpha_blend,
                cull: match params.cull_face {
                    CullFace::Nothing => 0,
                    CullFace::Front => 1,
                    CullFace::Back => 2,
                },
                winding: match params.front_face_order {
                    FrontFaceOrder::Clockwise => 0,
                    FrontFaceOrder::CounterClockwise => 1,
                },
                depth_stencil_state,
                primitive: params.primitive_type,
                _shader: shader,
            };

            self.pipelines.push(pipeline);

            Pipeline(self.pipelines.len() - 1)
        }
    }

    fn apply_pipeline(&mut self, pipeline: &Pipeline) {
        assert!(
            self.render_encoder.is_some(),
            "apply_pipeline before begin_pass"
        );
        let render_encoder = self.render_encoder.unwrap();
        let key = self.current_pass_key.expect("pass key");
        let view = self.view;
        let device = self.device;

        unsafe {
            self.current_pipeline = Some(*pipeline);
            let pipeline = &mut self.pipelines[pipeline.0];
            let state = match pipeline.variants.iter().find(|v| v.0 == key) {
                Some(v) => v.1,
                None => {
                    let _ = view;
                    let state = build_pipeline_variant(device, pipeline, &key);
                    pipeline.variants.push((key, state));
                    state
                }
            };

            msg_send_![render_encoder, setRenderPipelineState: state];
            msg_send_![render_encoder, setDepthStencilState:pipeline.depth_stencil_state];
            msg_send_![render_encoder, setFrontFacingWinding: pipeline.winding];
            msg_send_![render_encoder, setCullMode: pipeline.cull];
        }
    }

    fn apply_bindings_from_slice(
        &mut self,
        vertex_buffers: &[BufferId],
        index_buffer: BufferId,
        textures: &[TextureId],
    ) {
        assert!(
            self.render_encoder.is_some(),
            "apply_bindings before begin_pass"
        );

        unsafe {
            let render_encoder = self.render_encoder.unwrap();
            for (index, vertex_buffer) in vertex_buffers.iter().enumerate() {
                let buffer = &mut self.buffers[vertex_buffer.0];
                let () = msg_send![render_encoder,
                                   setVertexBuffer:buffer.raw[buffer.value]
                                   offset:0
                                   atIndex:(index + 1) as u64];
                buffer.next_value = buffer.value + 1;
            }
            let index_buffer = &mut self.buffers[index_buffer.0];
            self.index_buffer = Some(index_buffer.raw[index_buffer.value]);
            self.index_size = if index_buffer.element_size == 4 { 4 } else { 2 };
            index_buffer.next_value = index_buffer.value + 1;

            let img_count = textures.len();
            if img_count > 0 {
                for (n, img) in textures.iter().enumerate() {
                    let Texture {
                        sampler, texture, ..
                    } = self.textures.get(*img);
                    // Metal has 16 sampler slots; shaders past that use constexpr samplers.
                    if n < 16 {
                        msg_send_![render_encoder, setFragmentSamplerState:sampler
                                   atIndex:n
                        ];
                    }
                    msg_send_![render_encoder, setFragmentTexture:texture
                               atIndex:n
                    ];
                }
            }
        }
    }

    fn apply_uniforms_from_bytes(&mut self, uniform_ptr: *const u8, size: usize) {
        assert!(
            self.current_pipeline.is_some(),
            "apply_uniforms before apply_pipeline"
        );
        assert!(
            self.render_encoder.is_some(),
            "apply_uniforms before begin_pass"
        );

        let render_encoder = self.render_encoder.unwrap();

        self.current_frame_index = (self.current_frame_index + 1) % NUM_INFLIGHT_FRAMES;

        assert!(size < MAX_UNIFORM_BUFFER_SIZE as usize);

        assert!(self.current_ub_offset < MAX_UNIFORM_BUFFER_SIZE);

        let buffer = self.uniform_buffers[self.current_frame_index];
        unsafe {
            let dest: *mut std::ffi::c_void = msg_send![buffer, contents];
            std::ptr::copy(
                uniform_ptr as _,
                dest.add(self.current_ub_offset as usize),
                size,
            );

            #[cfg(target_os = "macos")]
            msg_send_![buffer, didModifyRange:NSRange::new(0, size as u64)];

            msg_send_![render_encoder,
                       setVertexBuffer:buffer
                       offset:self.current_ub_offset
                       atIndex:0];
            msg_send_![render_encoder,
                       setFragmentBuffer:buffer
                       offset:self.current_ub_offset
                       atIndex:0];
        }
        self.current_ub_offset = roundup_ub_buffer(self.current_ub_offset + size as u64);
    }

    fn begin_default_pass(&mut self, action: PassAction) {
        self.begin_pass(None, action)
    }

    fn begin_pass(&mut self, pass: Option<RenderPass>, action: PassAction) {
        unsafe {
            if self.command_buffer.is_none() {
                self.command_buffer = Some(msg_send![self.command_queue, commandBuffer]);
            }

            let (descriptor, key) = match pass {
                None => {
                    let color: u64 = msg_send![self.view, colorPixelFormat];
                    let samples: u64 = msg_send![self.view, sampleCount];
                    let depth: u64 = msg_send![self.view, depthStencilPixelFormat];
                    let stencil = if depth == MTLPixelFormat::Depth32Float_Stencil8 as u64 { depth } else { 0 };
                    (
                        msg_send_![self.view, currentRenderPassDescriptor],
                        PassKey { colors: [color, 0, 0, 0, 0, 0, 0, 0], n: 1, samples, depth, stencil },
                    )
                }
                Some(pass) => {
                    let pass = &self.passes[pass.0];
                    let mut key = PassKey { colors: [0; 8], n: pass.texture.len(), samples: 1, depth: 0, stencil: 0 };
                    for (i, t) in pass.texture.iter().enumerate() {
                        let p = self.textures.get(*t).params;
                        key.colors[i] = MTLPixelFormat::from(p.format) as u64;
                        key.samples = p.sample_count.max(1) as u64;
                    }
                    if let Some(d) = pass._depth_texture {
                        let p = self.textures.get(d).params;
                        key.depth = MTLPixelFormat::from(p.format) as u64;
                        if p.format == TextureFormat::Depth {
                            key.stencil = key.depth;
                        }
                        if pass.texture.is_empty() {
                            key.samples = p.sample_count.max(1) as u64;
                        }
                    }
                    (pass.render_pass_desc, key)
                }
            };
            assert!(!descriptor.is_null());
            self.current_pass_key = Some(key);

            let color_attachments = msg_send_![descriptor, colorAttachments];
            if key.n > 0 {
                let color_attachment = msg_send_![color_attachments, objectAtIndexedSubscript: 0];
                if pass.is_none() {
                    let store = if key.samples > 1 { MTLStoreAction::StoreAndMultisampleResolve } else { MTLStoreAction::Store };
                    msg_send_![color_attachment, setStoreAction: store];
                }
                match action {
                    PassAction::Clear { color, .. } => {
                        for i in 0..key.n {
                            let a = msg_send_![color_attachments, objectAtIndexedSubscript: i];
                            msg_send_![a, setLoadAction: MTLLoadAction::Clear];
                            if let Some(color) = color {
                                msg_send_![a, setClearColor:MTLClearColor::new(color.0 as _, color.1 as _, color.2 as _, color.3 as _)];
                            }
                        }
                    }
                    PassAction::Nothing => {
                        for i in 0..key.n {
                            let a = msg_send_![color_attachments, objectAtIndexedSubscript: i];
                            msg_send_![a, setLoadAction: MTLLoadAction::Load];
                        }
                    }
                }
            }
            if key.depth != 0 {
                let depth_attachment = msg_send_![descriptor, depthAttachment];
                if pass.is_none() {
                    msg_send_![depth_attachment, setStoreAction: MTLStoreAction::Store];
                }
                match action {
                    PassAction::Clear { depth, .. } => {
                        msg_send_![depth_attachment, setLoadAction: MTLLoadAction::Clear];
                        msg_send_![depth_attachment, setClearDepth: depth.unwrap_or(1.0) as f64];
                    }
                    PassAction::Nothing => {
                        msg_send_![depth_attachment, setLoadAction: MTLLoadAction::Load];
                    }
                }
            }

            let render_encoder = msg_send_![
                self.command_buffer.unwrap(),
                renderCommandEncoderWithDescriptor: descriptor
            ];

            self.render_encoder = Some(render_encoder);
        }
    }

    fn end_render_pass(&mut self) {
        assert!(
            self.render_encoder.is_some(),
            "end_render_pass unpaired with begin_render_pass!"
        );

        let render_encoder = self.render_encoder.unwrap();
        unsafe { msg_send_!(render_encoder, endEncoding) };

        self.render_encoder = None;
        self.index_buffer = None;
    }

    fn draw(&self, base_element: i32, num_elements: i32, num_instances: i32) {
        assert!(self.render_encoder.is_some(), "draw before begin_pass!");
        let render_encoder = self.render_encoder.unwrap();
        assert!(self.index_buffer.is_some());
        let index_buffer = self.index_buffer.unwrap();
        let index_type = if self.index_size == 4 { MTLIndexType::UInt32 } else { MTLIndexType::UInt16 };
        let primitive: MTLPrimitiveType = self.pipelines[self.current_pipeline.expect("pipeline").0].primitive.into();

        unsafe {
            msg_send_![render_encoder, drawIndexedPrimitives:primitive
                       indexCount:num_elements as u64
                       indexType:index_type
                       indexBuffer:index_buffer
                       indexBufferOffset:(base_element as u64 * self.index_size as u64)
                       instanceCount:num_instances as u64
                       baseVertex:0
                       baseInstance:0
            ];
        }
    }

    fn delete_shader(&mut self, _shader: ShaderId) {
        // TODO: place holder
    }
    fn delete_pipeline(&mut self, _pipeline: Pipeline) {
        // TODO: place holder
    }

    fn commit_frame(&mut self) {
        unsafe {
            assert!(!self.command_queue.is_null());
            if self.command_buffer.is_none() {
                self.command_buffer = Some(msg_send![self.command_queue, commandBuffer]);
            }
            let cb = self.command_buffer.unwrap();
            let drawable: ObjcId = msg_send!(self.view, currentDrawable);
            let mut capture = None;
            if self.capture_requested && !drawable.is_null() {
                self.capture_requested = false;
                let tex: ObjcId = msg_send![drawable, texture];
                let w: u64 = msg_send![tex, width];
                let h: u64 = msg_send![tex, height];
                let buf: ObjcId = msg_send![self.device, newBufferWithLength: w * h * 4
                                            options: MTLResourceOptions::StorageModeShared];
                let blit = msg_send_![cb, blitCommandEncoder];
                msg_send_![blit, copyFromTexture: tex
                           sourceSlice: 0u64
                           sourceLevel: 0u64
                           sourceOrigin: MTLOrigin { x: 0, y: 0, z: 0 }
                           sourceSize: MTLSize { width: w, height: h, depth: 1 }
                           toBuffer: buf
                           destinationOffset: 0u64
                           destinationBytesPerRow: w * 4
                           destinationBytesPerImage: w * h * 4];
                msg_send_![blit, endEncoding];
                capture = Some((buf, w, h));
            }
            msg_send_![cb, presentDrawable: drawable];
            msg_send_![cb, commit];
            msg_send_![cb, waitUntilCompleted];
            let t0: f64 = msg_send![cb, GPUStartTime];
            let t1: f64 = msg_send![cb, GPUEndTime];
            self.last_gpu_ms = (t1 - t0) * 1000.0;
            if let Some((buf, w, h)) = capture {
                let ptr: *const u8 = msg_send![buf, contents];
                let mut bytes = std::slice::from_raw_parts(ptr, (w * h * 4) as usize).to_vec();
                // BGRA -> RGBA, opaque.
                for px in bytes.chunks_exact_mut(4) {
                    px.swap(0, 2);
                    px[3] = 255;
                }
                msg_send_![buf, release];
                self.captured = Some((w as u32, h as u32, bytes));
            }
        }
        for buffer in &mut self.buffers {
            buffer.next_value = 0;
        }
        self.current_ub_offset = 0;
        self.current_pipeline = None;
        self.command_buffer = None;
        if (self.current_frame_index + 1) >= 3 {
            self.current_frame_index = 0;
        }
    }

    fn as_metal(&mut self) -> Option<&mut MetalContext> {
        Some(self)
    }

}
