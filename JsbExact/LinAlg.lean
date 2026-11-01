import JsbExact.Scalar

/-! `FGColumnVector3`, `FGMatrix33` and `FGQuaternion` operations with JSBSim's operation order. -/

namespace JsbExact
open S

variable {α : Type} [Scalar α]

structure V3 (α : Type) where
  x : α
  y : α
  z : α
  deriving Inhabited

/-- Row-major entries; JSBSim stores the same matrix column-major in `data[]`. -/
structure M33 (α : Type) where
  a11 : α
  a12 : α
  a13 : α
  a21 : α
  a22 : α
  a23 : α
  a31 : α
  a32 : α
  a33 : α
  deriving Inhabited

structure Quat (α : Type) where
  q0 : α
  q1 : α
  q2 : α
  q3 : α
  deriving Inhabited

@[inline] def V3.join (a b : V3 α) : V3 α := ⟨Scalar.join a.x b.x, Scalar.join a.y b.y, Scalar.join a.z b.z⟩
instance : Join α (V3 α) := ⟨V3.join⟩
instance : Join α (M33 α) := ⟨fun a b =>
  ⟨Scalar.join a.a11 b.a11, Scalar.join a.a12 b.a12, Scalar.join a.a13 b.a13, Scalar.join a.a21 b.a21,
   Scalar.join a.a22 b.a22, Scalar.join a.a23 b.a23, Scalar.join a.a31 b.a31, Scalar.join a.a32 b.a32,
   Scalar.join a.a33 b.a33⟩⟩
instance : Join α (Quat α) :=
  ⟨fun a b => ⟨Scalar.join a.q0 b.q0, Scalar.join a.q1 b.q1, Scalar.join a.q2 b.q2, Scalar.join a.q3 b.q3⟩⟩

namespace V3
@[inline] def zero : V3 α := ⟨S.zero, S.zero, S.zero⟩
@[inline] def add (a b : V3 α) : V3 α := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
@[inline] def sub (a b : V3 α) : V3 α := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
/-- `scalar * v` and `v * scalar`: `scalar*data[i]`. -/
@[inline] def smul (s : α) (v : V3 α) : V3 α := ⟨s * v.x, s * v.y, s * v.z⟩
/-- `operator*(FGColumnVector3)`: cross product. -/
@[inline] def cross (a b : V3 α) : V3 α :=
  ⟨msc a.y b.z (a.z * b.y), msc a.z b.x (a.x * b.z), msc a.x b.y (a.y * b.x)⟩
@[inline] def dot (a b : V3 α) : α := mac a.z b.z (mac a.x b.x (a.y * b.y))
@[inline] def mag (v : V3 α) : α := S.sqrt (mac v.z v.z (mac v.x v.x (v.y * v.y)))
/-- `Magnitude(idx1, idx2)` for indices 2, 3. -/
@[inline] def magYZ (v : V3 α) : α := S.sqrt (mac v.y v.y (v.z * v.z))
/-- `FGColumnVector3::operator/(scalar)`. -/
@[inline] def sdiv (v : V3 α) (s : α) : V3 α := sif S.ne s S.zero then smul (S.one / s) v else zero
end V3

namespace M33
@[inline] def mk' (a11 a12 a13 a21 a22 a23 a31 a32 a33 : α) : M33 α := ⟨a11, a12, a13, a21, a22, a23, a31, a32, a33⟩
@[inline] def zero : M33 α := mk' S.zero S.zero S.zero S.zero S.zero S.zero S.zero S.zero S.zero
@[inline] def T (m : M33 α) : M33 α := ⟨m.a11, m.a21, m.a31, m.a12, m.a22, m.a32, m.a13, m.a23, m.a33⟩
@[inline] def add (m n : M33 α) : M33 α :=
  ⟨m.a11 + n.a11, m.a12 + n.a12, m.a13 + n.a13, m.a21 + n.a21, m.a22 + n.a22, m.a23 + n.a23,
   m.a31 + n.a31, m.a32 + n.a32, m.a33 + n.a33⟩
/-- `FGMatrix33::operator*(const FGColumnVector3&)`: column-by-column accumulation. -/
@[inline] def mulV (m : M33 α) (v : V3 α) : V3 α :=
  let t1 := v.x * m.a11
  let t2 := v.x * m.a21
  let t3 := v.x * m.a31
  let t1 := mac v.y m.a12 t1
  let t2 := mac v.y m.a22 t2
  let t3 := mac v.y m.a32 t3
  ⟨mac v.z m.a13 t1, mac v.z m.a23 t2, mac v.z m.a33 t3⟩
@[inline] def e (a1 a2 a3 b1 b2 b3 : α) : α := mac a3 b3 (mac a1 b1 (a2 * b2))
/-- `FGMatrix33::operator*(const FGMatrix33&)`. -/
def mul (a b : M33 α) : M33 α :=
  ⟨e a.a11 a.a12 a.a13 b.a11 b.a21 b.a31, e a.a11 a.a12 a.a13 b.a12 b.a22 b.a32, e a.a11 a.a12 a.a13 b.a13 b.a23 b.a33,
   e a.a21 a.a22 a.a23 b.a11 b.a21 b.a31, e a.a21 a.a22 a.a23 b.a12 b.a22 b.a32, e a.a21 a.a22 a.a23 b.a13 b.a23 b.a33,
   e a.a31 a.a32 a.a33 b.a11 b.a21 b.a31, e a.a31 a.a32 a.a33 b.a12 b.a22 b.a32, e a.a31 a.a32 a.a33 b.a13 b.a23 b.a33⟩

/-- `FGMatrix33::GetEuler`: (phi, theta, psi). -/
def euler (m : M33 α) : V3 α :=
  let halfPi : α := lit (0.5 * 3.141592653589793)
  let locked (tht : α) : V3 α := ⟨S.atan2 (-m.a32) m.a22, tht, S.zero⟩
  sif S.le m.a13 (lit (-1.0)) then locked halfPi
  else sif S.le S.one m.a13 then locked (-halfPi)
  else
    let p := S.atan2 m.a12 m.a11
    ⟨S.atan2 m.a23 m.a33, S.asin (-m.a13), S.ite (S.lt p S.zero) (p + lit (2 * 3.141592653589793)) p⟩

/-- `FGMatrix33::GetQuaternion`. -/
def toQuat (m : M33 α) : Quat α :=
  let t0 := S.one + m.a11 + m.a22 + m.a33
  let t1 := S.one + m.a11 - m.a22 - m.a33
  let t2 := S.one - m.a11 + m.a22 - m.a33
  let t3 := S.one - m.a11 - m.a22 + m.a33
  let c1 := S.gt t1 t0
  let tm := S.ite c1 t1 t0
  let c2 := S.gt t2 tm
  let tm := S.ite c2 t2 tm
  let c3 := S.gt t3 tm
  let h : α := lit 0.5
  let qq : α := lit 0.25
  sif c3 then
    let q3 := h * S.sqrt t3
    ⟨qq * (m.a12 - m.a21) / q3, qq * (m.a13 + m.a31) / q3, qq * (m.a23 + m.a32) / q3, q3⟩
  else sif c2 then
    let q2 := h * S.sqrt t2
    ⟨qq * (m.a31 - m.a13) / q2, qq * (m.a12 + m.a21) / q2, q2, qq * (m.a23 + m.a32) / q2⟩
  else sif c1 then
    let q1 := h * S.sqrt t1
    ⟨qq * (m.a23 - m.a32) / q1, q1, qq * (m.a12 + m.a21) / q1, qq * (m.a31 + m.a13) / q1⟩
  else
    let q0 := h * S.sqrt t0
    ⟨q0, qq * (m.a23 - m.a32) / q0, qq * (m.a31 - m.a13) / q0, qq * (m.a12 - m.a21) / q0⟩
end M33

namespace Quat
@[inline] def add (a b : Quat α) : Quat α := ⟨a.q0 + b.q0, a.q1 + b.q1, a.q2 + b.q2, a.q3 + b.q3⟩
@[inline] def smul (s : α) (q : Quat α) : Quat α := ⟨s * q.q0, s * q.q1, s * q.q2, s * q.q3⟩
@[inline] def sqrMag (q : Quat α) : α := mac q.q3 q.q3 (mac q.q2 q.q2 (mac q.q0 q.q0 (q.q1 * q.q1)))

/-- `FGQuaternion::Normalize`. -/
def normalize (q : Quat α) : Quat α :=
  let n := S.sqrt (sqrMag q)
  sif S.cor (S.eq n S.zero) (S.lt (S.abs (n - S.one)) (lit 1e-10)) then q
  else let r := S.one / n; ⟨q.q0 * r, q.q1 * r, q.q2 * r, q.q3 * r⟩

/-- `FGQuaternion::GetQDot`. -/
def qdot (q : Quat α) (w : V3 α) : Quat α :=
  let h : α := lit 0.5
  ⟨lit (-0.5) * mac q.q3 w.z (mac q.q1 w.x (q.q2 * w.y)),
   h * mac q.q2 w.z (msc q.q0 w.x (q.q3 * w.y)),
   h * nmac q.q1 w.z (mac q.q3 w.x (q.q0 * w.y)),
   h * mac q.q0 w.z (mac (-q.q2) w.x (q.q1 * w.y))⟩

/-- `FGQuaternion::ComputeDerivedUnconditional`: the transformation matrix `mT`. -/
def toM (q : Quat α) : M33 α :=
  let q0q0 := q.q0 * q.q0
  let q1q1 := q.q1 * q.q1
  let q2q2 := q.q2 * q.q2
  let q3q3 := q.q3 * q.q3
  let q0q1 := q.q0 * q.q1
  let q0q2 := q.q0 * q.q2
  let q0q3 := q.q0 * q.q3
  let q1q2 := q.q1 * q.q2
  let q1q3 := q.q1 * q.q3
  let q2q3 := q.q2 * q.q3
  let two : α := lit 2.0
  ⟨q0q0 + q1q1 - q2q2 - q3q3, two * (q1q2 + q0q3), two * (q1q3 - q0q2),
   two * (q1q2 - q0q3), q0q0 - q1q1 + q2q2 - q3q3, two * (q2q3 + q0q1),
   two * (q1q3 + q0q2), two * (q2q3 - q0q1), q0q0 - q1q1 - q2q2 + q3q3⟩
end Quat

end JsbExact
