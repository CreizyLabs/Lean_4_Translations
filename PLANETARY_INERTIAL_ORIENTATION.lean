import ApolloMission.LEM_GEOMETRY

/-!
# Apollo 11 Luminary 1A (Build 099) — `PLANETARY_INERTIAL_ORIENTATION.agc` Formalization in Lean 4

Primary archival source:
- MIT Instrumentation Laboratory, *Luminary 1A (Rev. 001, Build 099, NASA 2021112-061)*,
  `PLANETARY_INERTIAL_ORIENTATION.agc`, Pages 1140–1148 (16:27 July 14, 1969).

Formalized routines:
1. `RP-TO-R` (Pages 1140–1141): Converts planetary-fixed vector `RP` (Earth-fixed if `MPAC = 0`,
   Moon-fixed if `MPAC ≠ 0`) to Basic Reference Inertial `R = M(T)ᵀ · (RP + LP × RP)`.
2. `R-TO-RP` (Pages 1142–1143): Inverse conversion `RP = M(T) · (R - L × R)`.
3. `MOONMX` & `MOONMXA` (Pages 1143–1145): Constructs the 3×3 Lunar Transformation Matrix `M`
   from `B`, `F`, `NODI`, and lunar equatorial inclination `I` (`1° 32.1'`) via `AVECTR`,
   `BVECTR`, `CVECTR`, and `DVECTR`.
4. `NEWANGLE` (Page 1145): Triple-precision split angle propagation `X = X0 + XDOT · (T + T0)`
   with `X1`-indexed scaling (`0` for `WEARTH`, `4` for `FDOT`, `5` for `NODDOT` and `BDOT`).
5. `EARTHMX` (Page 1146): Constructs the 3×3 Earth Z-rotation matrix `M(AZ)`.
6. `EARTHL` (Page 1147): Constructs the Earth polar-motion vector `L = (-AX, -AY, 0)`.

Verification guarantees:
- Zero `sorry`
- Zero custom `axiom`s
- Zero floating-point approximations (exact `SO(3)` proofs over arbitrary `ExactCommRing R`,
  exact Euler-angle factorization of `MOONMX`, exact first-order libration cancellation of
  `RP-TO-R` / `R-TO-RP`, and exact triple-precision bit-alignment proofs for `NEWANGLE`)
-/

namespace ApolloMission.PlanetaryInertialOrientation

open ApolloMission.LEMGeometry
open ApolloMission.LEMGeometry.ExactCommRing

-- ============================================================================
-- 1. EXACT 3D VECTOR & 3×3 MATRIX ALGEBRA OVER `ExactCommRing R`
-- ============================================================================

section RingLinearAlgebra

variable {R : Type} [ExactCommRing R]

local notation "zr" => ExactCommRing.zero
local notation "ur" => ExactCommRing.one
local infixl:65 " +ᵣ " => ExactCommRing.add
local prefix:75 "-ᵣ" => ExactCommRing.neg
local infixl:65 " -ᵣ " => ExactCommRing.sub
local infixl:70 " *ᵣ " => ExactCommRing.mul

/-- Exact 3×3 matrix stored by rows `(r0, r1, r2)`, matching AGC `MMATRIX` (`+0, +6, +12D`). -/
structure Mat3 (α : Type) where
  r0 : Vec3 α
  r1 : Vec3 α
  r2 : Vec3 α
  deriving Repr, DecidableEq

/-- Zero 3-vector. -/
def vecZero : Vec3 R := ⟨zr, zr, zr⟩

/-- Componentwise vector addition (`VAD`). -/
def vecAdd (u v : Vec3 R) : Vec3 R :=
  ⟨u.x +ᵣ v.x, u.y +ᵣ v.y, u.z +ᵣ v.z⟩

/-- Componentwise vector negation (`VCOMP`). -/
def vecNeg (u : Vec3 R) : Vec3 R :=
  ⟨-ᵣu.x, -ᵣu.y, -ᵣu.z⟩

/-- Componentwise vector subtraction (`VSU` / `BVSU`). -/
def vecSub (u v : Vec3 R) : Vec3 R :=
  ⟨u.x -ᵣ v.x, u.y -ᵣ v.y, u.z -ᵣ v.z⟩

/-- Scalar-vector multiplication (`VXSC`). -/
def vecScale (k : R) (u : Vec3 R) : Vec3 R :=
  ⟨k *ᵣ u.x, k *ᵣ u.y, k *ᵣ u.z⟩

/-- Exact 3D cross product `u × v` (`VXV`). -/
def vecCross (u v : Vec3 R) : Vec3 R :=
  ⟨(u.y *ᵣ v.z) -ᵣ (u.z *ᵣ v.y),
   (u.z *ᵣ v.x) -ᵣ (u.x *ᵣ v.z),
   (u.x *ᵣ v.y) -ᵣ (u.y *ᵣ v.x)⟩

/-- Identity 3×3 matrix `I₃`. -/
def matId : Mat3 R :=
  ⟨⟨ur, zr, zr⟩, ⟨zr, ur, zr⟩, ⟨zr, zr, ur⟩⟩

/-- Matrix transpose `Mᵀ`. -/
def matTranspose (m : Mat3 R) : Mat3 R :=
  ⟨⟨m.r0.x, m.r1.x, m.r2.x⟩,
   ⟨m.r0.y, m.r1.y, m.r2.y⟩,
   ⟨m.r0.z, m.r1.z, m.r2.z⟩⟩

/-- Matrix-column-vector product `M · v` (`MXV`). -/
def mxv (m : Mat3 R) (v : Vec3 R) : Vec3 R :=
  ⟨vec3Dot m.r0 v, vec3Dot m.r1 v, vec3Dot m.r2 v⟩

/-- Row-vector-matrix product `vᵀ · M = Mᵀ · v` (`VXM`). -/
def vxm (v : Vec3 R) (m : Mat3 R) : Vec3 R :=
  mxv (matTranspose m) v

/-- Matrix multiplication `A · B`. -/
def matMul (a b : Mat3 R) : Mat3 R :=
  let bt := matTranspose b
  ⟨⟨vec3Dot a.r0 bt.r0, vec3Dot a.r0 bt.r1, vec3Dot a.r0 bt.r2⟩,
   ⟨vec3Dot a.r1 bt.r0, vec3Dot a.r1 bt.r1, vec3Dot a.r1 bt.r2⟩,
   ⟨vec3Dot a.r2 bt.r0, vec3Dot a.r2 bt.r1, vec3Dot a.r2 bt.r2⟩⟩

/-- Determinant of a 3×3 matrix `det(M) = r0 · (r1 × r2)`. -/
def matDet (m : Mat3 R) : R :=
  vec3Dot m.r0 (vecCross m.r1 m.r2)

private theorem sub_zero (a : R) : a -ᵣ zr = a := by
  unfold ExactCommRing.sub; rw [ExactCommRing.neg_zero, add_zero]

private theorem add4_rearrange (a b c d : R) :
    (a +ᵣ b) +ᵣ (c +ᵣ d) = (a +ᵣ c) +ᵣ (b +ᵣ d) := by
  calc
    (a +ᵣ b) +ᵣ (c +ᵣ d) = a +ᵣ (b +ᵣ (c +ᵣ d)) := add_assoc _ _ _
    _ = a +ᵣ ((b +ᵣ c) +ᵣ d) := by rw [← add_assoc b c d]
    _ = a +ᵣ ((c +ᵣ b) +ᵣ d) := by rw [add_comm b c]
    _ = a +ᵣ (c +ᵣ (b +ᵣ d)) := by rw [add_assoc c b d]
    _ = (a +ᵣ c) +ᵣ (b +ᵣ d) := by rw [← add_assoc a c _]

private theorem add3_comm_mid (a b c : R) :
    (a +ᵣ b) +ᵣ c = (a +ᵣ c) +ᵣ b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

private theorem sum9_transpose (x1 x2 x3 y1 y2 y3 z1 z2 z3 : R) :
    (((((((x1 +ᵣ y1) +ᵣ z1) +ᵣ x2) +ᵣ y2) +ᵣ z2) +ᵣ x3) +ᵣ y3) +ᵣ z3 =
    (((((((x1 +ᵣ x2) +ᵣ x3) +ᵣ y1) +ᵣ y2) +ᵣ y3) +ᵣ z1) +ᵣ z2) +ᵣ z3 := by
  have p1 : ((x1 +ᵣ y1) +ᵣ z1) +ᵣ x2 = ((x1 +ᵣ x2) +ᵣ y1) +ᵣ z1 := by
    rw [add3_comm_mid (x1 +ᵣ y1) z1 x2, add3_comm_mid x1 y1 x2]
  rw [p1]
  have p2 : (((x1 +ᵣ x2) +ᵣ y1) +ᵣ z1) +ᵣ y2 = (((x1 +ᵣ x2) +ᵣ y1) +ᵣ y2) +ᵣ z1 := by
    rw [add3_comm_mid _ z1 y2]
  rw [p2]
  have p3 : (((((x1 +ᵣ x2) +ᵣ y1) +ᵣ y2) +ᵣ z1) +ᵣ z2) +ᵣ x3 =
      ((((((x1 +ᵣ x2) +ᵣ x3) +ᵣ y1) +ᵣ y2) +ᵣ z1) +ᵣ z2) := by
    rw [add3_comm_mid _ z2 x3, add3_comm_mid _ z1 x3, add3_comm_mid _ y2 x3, add3_comm_mid _ y1 x3]
  rw [p3]
  have p4 : ((((((x1 +ᵣ x2) +ᵣ x3) +ᵣ y1) +ᵣ y2) +ᵣ z1) +ᵣ z2) +ᵣ y3 =
      ((((((x1 +ᵣ x2) +ᵣ x3) +ᵣ y1) +ᵣ y2) +ᵣ y3) +ᵣ z1) +ᵣ z2 := by
    rw [add3_comm_mid _ z2 y3, add3_comm_mid _ z1 y3]
  rw [p4]

/-- Exact orthogonality of `u` and `v × u`: `u · (v × u) = 0`. -/
theorem vec3Dot_cross_right_self (u v : Vec3 R) :
    vec3Dot u (vecCross v u) = zr := by
  unfold vec3Dot vecCross ExactCommRing.sub
  rw [left_distrib, left_distrib, left_distrib, mul_neg, mul_neg, mul_neg]
  have h1 : u.x *ᵣ (v.y *ᵣ u.z) = u.z *ᵣ (v.y *ᵣ u.x) := by
    rw [← mul_assoc, mul_comm u.x v.y, mul_assoc, mul_comm u.x u.z, ← mul_assoc, mul_comm v.y u.z, mul_assoc]
  have h2 : u.x *ᵣ (v.z *ᵣ u.y) = u.y *ᵣ (v.z *ᵣ u.x) := by
    rw [← mul_assoc, mul_comm u.x v.z, mul_assoc, mul_comm u.x u.y, ← mul_assoc, mul_comm v.z u.y, mul_assoc]
  have h3 : u.y *ᵣ (v.x *ᵣ u.z) = u.z *ᵣ (v.x *ᵣ u.y) := by
    rw [← mul_assoc, mul_comm u.y v.x, mul_assoc, mul_comm u.y u.z, ← mul_assoc, mul_comm v.x u.z, mul_assoc]
  rw [h1, h2, h3]
  have hc (A B C : R) : ((A +ᵣ -ᵣB) +ᵣ (B +ᵣ -ᵣC)) +ᵣ (C +ᵣ -ᵣA) = zr := by
    calc
      ((A +ᵣ -ᵣB) +ᵣ (B +ᵣ -ᵣC)) +ᵣ (C +ᵣ -ᵣA)
        = (A +ᵣ ((-ᵣB +ᵣ B) +ᵣ -ᵣC)) +ᵣ (C +ᵣ -ᵣA) := by
            rw [add_assoc A (-ᵣB) (B +ᵣ -ᵣC), ← add_assoc (-ᵣB) B (-ᵣC)]
      _ = (A +ᵣ -ᵣC) +ᵣ (C +ᵣ -ᵣA) := by rw [add_left_neg, zero_add]
      _ = A +ᵣ ((-ᵣC +ᵣ C) +ᵣ -ᵣA) := by
            rw [add_assoc A (-ᵣC) (C +ᵣ -ᵣA), ← add_assoc (-ᵣC) C (-ᵣA)]
      _ = A +ᵣ -ᵣA := by rw [add_left_neg, zero_add]
      _ = zr := add_right_neg A
  exact hc _ _ _

/-- Exact cross-product linearity in the second argument: `w × (u + v) = (w × u) + (w × v)`. -/
theorem vecCross_add_right (w u v : Vec3 R) :
    vecCross w (vecAdd u v) = vecAdd (vecCross w u) (vecCross w v) := by
  unfold vecCross vecAdd ExactCommRing.sub
  congr 1 <;> (rw [left_distrib, left_distrib, neg_add]; exact add4_rearrange _ _ _ _)

/-- Exact cross-product linearity in subtraction: `w × (u - v) = (w × u) - (w × v)`. -/
theorem vecCross_sub_right (w u v : Vec3 R) :
    vecCross w (vecSub u v) = vecSub (vecCross w u) (vecCross w v) := by
  unfold vecCross vecSub ExactCommRing.sub
  congr 1 <;>
    (rw [left_distrib, left_distrib, mul_neg, mul_neg, neg_add, neg_add, neg_neg]
     exact add4_rearrange _ _ _ _)

theorem vecAdd_zero (u : Vec3 R) : vecAdd u vecZero = u := by
  cases u; simp [vecAdd, vecZero, add_zero]

theorem vecSub_zero (u : Vec3 R) : vecSub u vecZero = u := by
  cases u; simp [vecSub, vecZero, sub_zero]

theorem vecCross_zero_left (v : Vec3 R) : vecCross vecZero v = vecZero := by
  simp [vecCross, vecZero, zero_mul, sub_zero]

/-- Exact linearity of `mxv` over addition. -/
theorem mxv_add (m : Mat3 R) (u v : Vec3 R) :
    mxv m (vecAdd u v) = vecAdd (mxv m u) (mxv m v) := by
  unfold mxv vecAdd vec3Dot
  have hrow (r : Vec3 R) :
      ((r.x *ᵣ (u.x +ᵣ v.x)) +ᵣ (r.y *ᵣ (u.y +ᵣ v.y))) +ᵣ (r.z *ᵣ (u.z +ᵣ v.z)) =
      ((r.x *ᵣ u.x +ᵣ r.y *ᵣ u.y) +ᵣ r.z *ᵣ u.z) +ᵣ ((r.x *ᵣ v.x +ᵣ r.y *ᵣ v.y) +ᵣ r.z *ᵣ v.z) := by
    rw [left_distrib, left_distrib, left_distrib,
        add4_rearrange (r.x *ᵣ u.x) (r.x *ᵣ v.x) (r.y *ᵣ u.y) (r.y *ᵣ v.y),
        add4_rearrange]
  rw [hrow m.r0, hrow m.r1, hrow m.r2]

/-- Exact linearity of `mxv` over subtraction. -/
theorem mxv_sub (m : Mat3 R) (u v : Vec3 R) :
    mxv m (vecSub u v) = vecSub (mxv m u) (mxv m v) := by
  unfold mxv vecSub vec3Dot ExactCommRing.sub
  have hrow (r : Vec3 R) :
      ((r.x *ᵣ (u.x +ᵣ -ᵣv.x)) +ᵣ (r.y *ᵣ (u.y +ᵣ -ᵣv.y))) +ᵣ (r.z *ᵣ (u.z +ᵣ -ᵣv.z)) =
      ((r.x *ᵣ u.x +ᵣ r.y *ᵣ u.y) +ᵣ r.z *ᵣ u.z) +ᵣ -ᵣ((r.x *ᵣ v.x +ᵣ r.y *ᵣ v.y) +ᵣ r.z *ᵣ v.z) := by
    rw [left_distrib, left_distrib, left_distrib, mul_neg, mul_neg, mul_neg, neg_add, neg_add,
        add4_rearrange (r.x *ᵣ u.x) (-ᵣ(r.x *ᵣ v.x)) (r.y *ᵣ u.y) (-ᵣ(r.y *ᵣ v.y)),
        add4_rearrange]
  rw [hrow m.r0, hrow m.r1, hrow m.r2]

/-- Exact associativity of matrix-vector multiplication: `(A · B) · v = A · (B · v)`. -/
theorem mxv_matMul (a b : Mat3 R) (v : Vec3 R) :
    mxv (matMul a b) v = mxv a (mxv b v) := by
  unfold mxv matMul matTranspose vec3Dot
  have hrow (r : Vec3 R) :
      (((r.x *ᵣ b.r0.x +ᵣ r.y *ᵣ b.r1.x) +ᵣ r.z *ᵣ b.r2.x) *ᵣ v.x +ᵣ
       ((r.x *ᵣ b.r0.y +ᵣ r.y *ᵣ b.r1.y) +ᵣ r.z *ᵣ b.r2.y) *ᵣ v.y) +ᵣ
      ((r.x *ᵣ b.r0.z +ᵣ r.y *ᵣ b.r1.z) +ᵣ r.z *ᵣ b.r2.z) *ᵣ v.z =
      (r.x *ᵣ ((b.r0.x *ᵣ v.x +ᵣ b.r0.y *ᵣ v.y) +ᵣ b.r0.z *ᵣ v.z) +ᵣ
       r.y *ᵣ ((b.r1.x *ᵣ v.x +ᵣ b.r1.y *ᵣ v.y) +ᵣ b.r1.z *ᵣ v.z)) +ᵣ
      r.z *ᵣ ((b.r2.x *ᵣ v.x +ᵣ b.r2.y *ᵣ v.y) +ᵣ b.r2.z *ᵣ v.z) := by
    simp only [left_distrib, right_distrib, mul_assoc]
    repeat rw [← add_assoc]
    exact sum9_transpose _ _ _ _ _ _ _ _ _
  rw [hrow a.r0, hrow a.r1, hrow a.r2]

theorem mxv_id (v : Vec3 R) : mxv matId v = v := by
  cases v
  simp [mxv, matId, vec3Dot, one_mul, zero_mul, add_zero, zero_add]

omit [ExactCommRing R] in
theorem matTranspose_involutive (m : Mat3 R) : matTranspose (matTranspose m) = m := by
  cases m with | mk r0 r1 r2 =>
  cases r0; cases r1; cases r2; rfl

theorem matTranspose_mul (a b : Mat3 R) :
    matTranspose (matMul a b) = matMul (matTranspose b) (matTranspose a) := by
  unfold matTranspose matMul vec3Dot
  have hdot (p q : Vec3 R) :
      (p.x *ᵣ q.x +ᵣ p.y *ᵣ q.y) +ᵣ p.z *ᵣ q.z = (q.x *ᵣ p.x +ᵣ q.y *ᵣ p.y) +ᵣ q.z *ᵣ p.z := by
    rw [mul_comm p.x q.x, mul_comm p.y q.y, mul_comm p.z q.z]
  congr 1 <;> congr 1 <;> apply hdot

theorem matMul_assoc (a b c : Mat3 R) :
    matMul (matMul a b) c = matMul a (matMul b c) := by
  have hcol (v : Vec3 R) : mxv (matMul (matMul a b) c) v = mxv (matMul a (matMul b c)) v := by
    rw [mxv_matMul, mxv_matMul, mxv_matMul, mxv_matMul]
  have col_x (m : Mat3 R) : mxv m ⟨ur, zr, zr⟩ = ⟨m.r0.x, m.r1.x, m.r2.x⟩ := by
    simp [mxv, vec3Dot, mul_one, mul_zero, add_zero]
  have col_y (m : Mat3 R) : mxv m ⟨zr, ur, zr⟩ = ⟨m.r0.y, m.r1.y, m.r2.y⟩ := by
    simp [mxv, vec3Dot, mul_one, mul_zero, add_zero, zero_add]
  have col_z (m : Mat3 R) : mxv m ⟨zr, zr, ur⟩ = ⟨m.r0.z, m.r1.z, m.r2.z⟩ := by
    simp [mxv, vec3Dot, mul_one, mul_zero, add_zero, zero_add]
  have hx := hcol ⟨ur, zr, zr⟩
  have hy := hcol ⟨zr, ur, zr⟩
  have hz := hcol ⟨zr, zr, ur⟩
  rw [col_x, col_x] at hx
  rw [col_y, col_y] at hy
  rw [col_z, col_z] at hz
  injection hx with hx0 hx1 hx2
  injection hy with hy0 hy1 hy2
  injection hz with hz0 hz1 hz2
  cases hL : matMul (matMul a b) c with | mk l0 l1 l2 =>
  cases hR : matMul a (matMul b c) with | mk r0 r1 r2 =>
  cases l0; cases l1; cases l2; cases r0; cases r1; cases r2
  rw [hL, hR] at hx0 hx1 hx2 hy0 hy1 hy2 hz0 hz1 hz2
  simp_all

theorem matMul_id_left (m : Mat3 R) : matMul matId m = m := by
  cases m with | mk r0 r1 r2 =>
  cases r0; cases r1; cases r2
  simp [matMul, matId, matTranspose, vec3Dot, one_mul, zero_mul, add_zero, zero_add]

theorem matMul_id_right (m : Mat3 R) : matMul m matId = m := by
  cases m with | mk r0 r1 r2 =>
  cases r0; cases r1; cases r2
  simp [matMul, matId, matTranspose, vec3Dot, mul_one, mul_zero, add_zero, zero_add]

/-- Proper orthogonal rotation matrix bundle `SO3 R` (zero custom axioms). -/
structure SO3 (R : Type) [ExactCommRing R] where
  mat : Mat3 R
  mul_transpose : matMul mat (matTranspose mat) = matId
  transpose_mul : matMul (matTranspose mat) mat = matId
  det_one : matDet mat = ExactCommRing.one
  preserves_cross : ∀ u v : Vec3 R, mxv mat (vecCross u v) = vecCross (mxv mat u) (mxv mat v)

theorem SO3.preserves_dot (m : SO3 R) (u v : Vec3 R) :
    vec3Dot (mxv m.mat u) (mxv m.mat v) = vec3Dot u v := by
  have h1 (a : Mat3 R) (x y : Vec3 R) :
      vec3Dot (mxv a x) y = vec3Dot x (mxv (matTranspose a) y) := by
    unfold mxv matTranspose
    simp only [vec3Dot, left_distrib, right_distrib, mul_assoc]
    repeat rw [← add_assoc]
    have mc (p q r : R) : p *ᵣ (q *ᵣ r) = q *ᵣ (p *ᵣ r) := by
      rw [← mul_assoc, mul_comm p q, mul_assoc]
    rw [sum9_transpose]
    rw [mc a.r0.x x.x y.x, mc a.r1.x x.x y.y, mc a.r2.x x.x y.z,
        mc a.r0.y x.y y.x, mc a.r1.y x.y y.y, mc a.r2.y x.y y.z,
        mc a.r0.z x.z y.x, mc a.r1.z x.z y.y, mc a.r2.z x.z y.z]
  rw [h1 m.mat u (mxv m.mat v), ← mxv_matMul, m.transpose_mul, mxv_id]

theorem SO3.preserves_norm_sq (m : SO3 R) (u : Vec3 R) :
    vec3NormSq (mxv m.mat u) = vec3NormSq u :=
  m.preserves_dot u u

theorem SO3.mxv_vxm (m : SO3 R) (v : Vec3 R) :
    mxv m.mat (vxm v m.mat) = v := by
  unfold vxm
  rw [← mxv_matMul, m.mul_transpose, mxv_id]

theorem SO3.vxm_mxv (m : SO3 R) (v : Vec3 R) :
    vxm (mxv m.mat v) m.mat = v := by
  unfold vxm
  rw [← mxv_matMul, m.transpose_mul, mxv_id]

private theorem matDet_mul_of_preserves_cross (a b : Mat3 R)
    (hcross : ∀ u v : Vec3 R, mxv a (vecCross u v) = vecCross (mxv a u) (mxv a v))
    (hdot : ∀ u v : Vec3 R, vec3Dot (mxv a u) (mxv a v) = vec3Dot u v) :
    matDet (matMul a b) = matDet b := by
  have det_eq_cols (m : Mat3 R) :
      matDet m = vec3Dot (matTranspose m).r0 (vecCross (matTranspose m).r1 (matTranspose m).r2) := by
    unfold matDet matTranspose vec3Dot vecCross ExactCommRing.sub
    simp only [left_distrib, mul_neg]
    repeat rw [← add_assoc]
    have e2 : m.r0.x *ᵣ (m.r1.z *ᵣ m.r2.y) = m.r0.x *ᵣ (m.r2.y *ᵣ m.r1.z) := by rw [mul_comm m.r1.z m.r2.y]
    have e3 : m.r0.y *ᵣ (m.r1.z *ᵣ m.r2.x) = m.r2.x *ᵣ (m.r0.y *ᵣ m.r1.z) := by
      rw [← mul_assoc, mul_comm m.r0.y m.r1.z, mul_assoc, mul_comm m.r0.y m.r2.x,
          ← mul_assoc, mul_comm m.r1.z m.r2.x, mul_assoc, mul_comm m.r1.z m.r0.y]
    have e4 : m.r0.y *ᵣ (m.r1.x *ᵣ m.r2.z) = m.r1.x *ᵣ (m.r0.y *ᵣ m.r2.z) := by
      rw [← mul_assoc, mul_comm m.r0.y m.r1.x, mul_assoc]
    have e5 : m.r0.z *ᵣ (m.r1.x *ᵣ m.r2.y) = m.r1.x *ᵣ (m.r2.y *ᵣ m.r0.z) := by
      rw [← mul_assoc, mul_comm m.r0.z m.r1.x, mul_assoc, mul_comm m.r0.z m.r2.y]
    have e6 : m.r0.z *ᵣ (m.r1.y *ᵣ m.r2.x) = m.r2.x *ᵣ (m.r1.y *ᵣ m.r0.z) := by
      rw [← mul_assoc, mul_comm m.r0.z m.r1.y, mul_assoc, mul_comm m.r0.z m.r2.x,
          ← mul_assoc, mul_comm m.r1.y m.r2.x, mul_assoc]
    rw [e2, e3, e4, e5, e6]
    have perm6 (t1 t2 t3 t4 t5 t6 : R) :
        ((((t1 +ᵣ t2) +ᵣ t3) +ᵣ t4) +ᵣ t5) +ᵣ t6 =
        ((((t1 +ᵣ t2) +ᵣ t5) +ᵣ t4) +ᵣ t3) +ᵣ t6 := by
      rw [add3_comm_mid _ t4 t5, add3_comm_mid _ t3 t5, add3_comm_mid _ t3 t4]
    exact perm6 _ _ _ _ _ _
  rw [det_eq_cols (matMul a b), det_eq_cols b]
  have hcol0 : (matTranspose (matMul a b)).r0 = mxv a (matTranspose b).r0 := by simp [matTranspose, matMul, mxv]
  have hcol1 : (matTranspose (matMul a b)).r1 = mxv a (matTranspose b).r1 := by simp [matTranspose, matMul, mxv]
  have hcol2 : (matTranspose (matMul a b)).r2 = mxv a (matTranspose b).r2 := by simp [matTranspose, matMul, mxv]
  rw [hcol0, hcol1, hcol2, ← hcross, hdot]

def SO3.comp (a b : SO3 R) : SO3 R where
  mat := matMul a.mat b.mat
  mul_transpose := by
    rw [matTranspose_mul, matMul_assoc, ← matMul_assoc b.mat, b.mul_transpose,
        matMul_id_left, a.mul_transpose]
  transpose_mul := by
    rw [matTranspose_mul, matMul_assoc, ← matMul_assoc (matTranspose a.mat), a.transpose_mul,
        matMul_id_left, b.transpose_mul]
  det_one := by
    rw [matDet_mul_of_preserves_cross a.mat b.mat a.preserves_cross a.preserves_dot, b.det_one]
  preserves_cross := by
    intro u v
    rw [mxv_matMul, mxv_matMul, mxv_matMul, b.preserves_cross, a.preserves_cross]

def SO3.inv (a : SO3 R) : SO3 R where
  mat := matTranspose a.mat
  mul_transpose := by rw [matTranspose_involutive]; exact a.transpose_mul
  transpose_mul := by rw [matTranspose_involutive]; exact a.mul_transpose
  det_one := by
    have h := matDet_mul_of_preserves_cross a.mat (matTranspose a.mat) a.preserves_cross a.preserves_dot
    rw [a.mul_transpose] at h
    have hid : matDet (matId : Mat3 R) = ur := by
      simp [matDet, matId, vec3Dot, vecCross, ExactCommRing.sub, one_mul, zero_mul, add_zero, zero_add, neg_zero]
    rw [hid] at h
    exact h.symm
  preserves_cross := by
    intro u v
    have h := congrArg (fun w => mxv (matTranspose a.mat) w)
      (a.preserves_cross (mxv (matTranspose a.mat) u) (mxv (matTranspose a.mat) v))
    have hu : mxv a.mat (mxv (matTranspose a.mat) u) = u := by
      rw [← mxv_matMul, a.mul_transpose, mxv_id]
    have hv : mxv a.mat (mxv (matTranspose a.mat) v) = v := by
      rw [← mxv_matMul, a.mul_transpose, mxv_id]
    have hlhs : mxv (matTranspose a.mat) (mxv a.mat (vecCross (mxv (matTranspose a.mat) u) (mxv (matTranspose a.mat) v))) =
        vecCross (mxv (matTranspose a.mat) u) (mxv (matTranspose a.mat) v) := by
      rw [← mxv_matMul, a.transpose_mul, mxv_id]
    dsimp only at h
    rw [hu, hv, hlhs] at h
    exact h.symm

-- ============================================================================
-- 2. ELEMENTARY ROTATIONS IN `SO3` (Z-ROTATION & X-ROTATION)
-- ============================================================================

/-- Elementary Z-axis rotation `Rz(θ)` matching `EARTHMX` (`Page 1146`). -/
def rotZMat (θ : TrigAngle R) : Mat3 R :=
  ⟨⟨θ.c, θ.s, zr⟩,
   ⟨-ᵣθ.s, θ.c, zr⟩,
   ⟨zr, zr, ur⟩⟩

/-- Proof that `rotZMat θ` lies in `SO3 R` universally over any `ExactCommRing R`. -/
def rotZ (θ : TrigAngle R) : SO3 R where
  mat := rotZMat θ
  mul_transpose := by
    unfold matMul matTranspose rotZMat matId vec3Dot
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, neg_mul_neg, neg_mul, mul_neg, neg_neg, neg_zero]
    have hcs : θ.c *ᵣ θ.s = θ.s *ᵣ θ.c := mul_comm _ _
    congr 1
    · congr 1
      · exact θ.unit
      · rw [hcs, add_left_neg]
    · congr 1
      · rw [hcs, add_left_neg]
      · rw [add_comm]; exact θ.unit
  transpose_mul := by
    unfold matMul matTranspose rotZMat matId vec3Dot
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, neg_mul_neg, neg_mul, mul_neg, neg_neg, neg_zero]
    have hcs : θ.c *ᵣ θ.s = θ.s *ᵣ θ.c := mul_comm _ _
    congr 1
    · congr 1
      · exact θ.unit
      · rw [hcs, add_right_neg]
    · congr 1
      · rw [hcs, add_right_neg]
      · rw [add_comm]; exact θ.unit
  det_one := by
    unfold matDet rotZMat vec3Dot vecCross ExactCommRing.sub
    simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_zero, neg_mul_neg, neg_mul, mul_neg, neg_neg]
    exact θ.unit
  preserves_cross := by
    intro u v
    unfold mxv rotZMat vecCross vec3Dot ExactCommRing.sub
    simp only [zero_mul, one_mul, add_zero, zero_add, neg_zero, neg_mul, mul_neg, neg_neg, left_distrib, right_distrib, neg_add]
    congr 1
    · have t1 : θ.c *ᵣ (u.y *ᵣ v.z) = (θ.c *ᵣ u.y) *ᵣ v.z := (mul_assoc _ _ _).symm
      have t2 : θ.c *ᵣ (u.z *ᵣ v.y) = u.z *ᵣ (θ.c *ᵣ v.y) := by
        rw [← mul_assoc, mul_comm θ.c u.z, mul_assoc]
      have t3 : θ.s *ᵣ (u.z *ᵣ v.x) = u.z *ᵣ (θ.s *ᵣ v.x) := by
        rw [← mul_assoc, mul_comm θ.s u.z, mul_assoc]
      have t4 : θ.s *ᵣ (u.x *ᵣ v.z) = (θ.s *ᵣ u.x) *ᵣ v.z := (mul_assoc _ _ _).symm
      rw [t1, t2, t3, t4]
      have h4 (a b c d : R) : (a +ᵣ -ᵣb) +ᵣ (c +ᵣ -ᵣd) = (-ᵣd +ᵣ a) +ᵣ (c +ᵣ -ᵣb) := by
        calc
          (a +ᵣ -ᵣb) +ᵣ (c +ᵣ -ᵣd)
            = (a +ᵣ -ᵣb) +ᵣ (-ᵣd +ᵣ c) := by rw [add_comm c (-ᵣd)]
          _ = (a +ᵣ -ᵣd) +ᵣ (-ᵣb +ᵣ c) := add4_rearrange _ _ _ _
          _ = (-ᵣd +ᵣ a) +ᵣ (c +ᵣ -ᵣb) := by rw [add_comm a (-ᵣd), add_comm (-ᵣb) c]
      exact h4 _ _ _ _
    · have t1 : θ.s *ᵣ (u.y *ᵣ v.z) = (θ.s *ᵣ u.y) *ᵣ v.z := (mul_assoc _ _ _).symm
      have t2 : θ.s *ᵣ (u.z *ᵣ v.y) = u.z *ᵣ (θ.s *ᵣ v.y) := by
        rw [← mul_assoc, mul_comm θ.s u.z, mul_assoc]
      have t3 : θ.c *ᵣ (u.z *ᵣ v.x) = u.z *ᵣ (θ.c *ᵣ v.x) := by
        rw [← mul_assoc, mul_comm θ.c u.z, mul_assoc]
      have t4 : θ.c *ᵣ (u.x *ᵣ v.z) = (θ.c *ᵣ u.x) *ᵣ v.z := (mul_assoc _ _ _).symm
      rw [t1, t2, t3, t4]
      have h4' (a b c d : R) : (-ᵣa +ᵣ b) +ᵣ (c +ᵣ -ᵣd) = (c +ᵣ b) +ᵣ (-ᵣd +ᵣ -ᵣa) := by
        calc
          (-ᵣa +ᵣ b) +ᵣ (c +ᵣ -ᵣd)
            = (b +ᵣ -ᵣa) +ᵣ (c +ᵣ -ᵣd) := by rw [add_comm (-ᵣa) b]
          _ = (b +ᵣ c) +ᵣ (-ᵣa +ᵣ -ᵣd) := add4_rearrange _ _ _ _
          _ = (c +ᵣ b) +ᵣ (-ᵣd +ᵣ -ᵣa) := by rw [add_comm b c, add_comm (-ᵣa) (-ᵣd)]
      exact h4' _ _ _ _
    · have c1 : (θ.c *ᵣ u.x) *ᵣ (θ.c *ᵣ v.y) = (θ.c *ᵣ θ.c) *ᵣ (u.x *ᵣ v.y) := by
        rw [mul_assoc, ← mul_assoc u.x θ.c v.y, mul_comm u.x θ.c, mul_assoc θ.c u.x v.y, ← mul_assoc]
      have c2 : (θ.s *ᵣ u.y) *ᵣ (θ.s *ᵣ v.x) = (θ.s *ᵣ θ.s) *ᵣ (u.y *ᵣ v.x) := by
        rw [mul_assoc, ← mul_assoc u.y θ.s v.x, mul_comm u.y θ.s, mul_assoc θ.s u.y v.x, ← mul_assoc]
      have c3 : (θ.s *ᵣ u.x) *ᵣ (θ.s *ᵣ v.y) = (θ.s *ᵣ θ.s) *ᵣ (u.x *ᵣ v.y) := by
        rw [mul_assoc, ← mul_assoc u.x θ.s v.y, mul_comm u.x θ.s, mul_assoc θ.s u.x v.y, ← mul_assoc]
      have c4 : (θ.c *ᵣ u.y) *ᵣ (θ.c *ᵣ v.x) = (θ.c *ᵣ θ.c) *ᵣ (u.y *ᵣ v.x) := by
        rw [mul_assoc, ← mul_assoc u.y θ.c v.x, mul_comm u.y θ.c, mul_assoc θ.c u.y v.x, ← mul_assoc]
      have m1 : (θ.c *ᵣ u.x) *ᵣ (θ.s *ᵣ v.x) = (θ.s *ᵣ u.x) *ᵣ (θ.c *ᵣ v.x) := by
        calc
          (θ.c *ᵣ u.x) *ᵣ (θ.s *ᵣ v.x)
            = θ.c *ᵣ (u.x *ᵣ (θ.s *ᵣ v.x)) := mul_assoc _ _ _
          _ = θ.c *ᵣ ((θ.s *ᵣ u.x) *ᵣ v.x) := by rw [← mul_assoc u.x θ.s v.x, mul_comm u.x θ.s]
          _ = (θ.c *ᵣ (θ.s *ᵣ u.x)) *ᵣ v.x := (mul_assoc _ _ _).symm
          _ = ((θ.s *ᵣ u.x) *ᵣ θ.c) *ᵣ v.x := by rw [mul_comm θ.c (θ.s *ᵣ u.x)]
          _ = (θ.s *ᵣ u.x) *ᵣ (θ.c *ᵣ v.x) := mul_assoc _ _ _
      have m2 : (θ.s *ᵣ u.y) *ᵣ (θ.c *ᵣ v.y) = (θ.c *ᵣ u.y) *ᵣ (θ.s *ᵣ v.y) := by
        calc
          (θ.s *ᵣ u.y) *ᵣ (θ.c *ᵣ v.y)
            = θ.s *ᵣ (u.y *ᵣ (θ.c *ᵣ v.y)) := mul_assoc _ _ _
          _ = θ.s *ᵣ ((θ.c *ᵣ u.y) *ᵣ v.y) := by rw [← mul_assoc u.y θ.c v.y, mul_comm u.y θ.c]
          _ = (θ.s *ᵣ (θ.c *ᵣ u.y)) *ᵣ v.y := (mul_assoc _ _ _).symm
          _ = ((θ.c *ᵣ u.y) *ᵣ θ.s) *ᵣ v.y := by rw [mul_comm θ.s (θ.c *ᵣ u.y)]
          _ = (θ.c *ᵣ u.y) *ᵣ (θ.s *ᵣ v.y) := mul_assoc _ _ _
      rw [c1, c2, c3, c4, m1, m2]
      have hfactor : u.x *ᵣ v.y +ᵣ -ᵣ(u.y *ᵣ v.x) =
          ((θ.c *ᵣ θ.c) *ᵣ (u.x *ᵣ v.y) +ᵣ (θ.s *ᵣ θ.s) *ᵣ (u.x *ᵣ v.y)) +ᵣ
          (-ᵣ((θ.c *ᵣ θ.c) *ᵣ (u.y *ᵣ v.x)) +ᵣ -ᵣ((θ.s *ᵣ θ.s) *ᵣ (u.y *ᵣ v.x))) := by
        rw [← right_distrib, ← neg_add, ← right_distrib, θ.unit, one_mul, one_mul]
      rw [hfactor]
      have hcancel (p1 p2 q1 q2 k1 k2 : R) :
          ((-ᵣk1 +ᵣ -ᵣq2) +ᵣ (p1 +ᵣ k2)) +ᵣ ((k1 +ᵣ -ᵣq1) +ᵣ (p2 +ᵣ -ᵣk2)) =
          (p1 +ᵣ p2) +ᵣ (-ᵣq1 +ᵣ -ᵣq2) := by
        rw [add4_rearrange (-ᵣk1 +ᵣ -ᵣq2) (p1 +ᵣ k2) (k1 +ᵣ -ᵣq1) (p2 +ᵣ -ᵣk2)]
        rw [add4_rearrange (-ᵣk1) (-ᵣq2) k1 (-ᵣq1), add_left_neg, zero_add]
        rw [add4_rearrange p1 k2 p2 (-ᵣk2), add_right_neg, add_zero]
        rw [add_comm (-ᵣq2 +ᵣ -ᵣq1) (p1 +ᵣ p2), add_comm (-ᵣq2) (-ᵣq1)]
      exact (hcancel _ _ _ _ _ _).symm

/-- Elementary X-axis rotation `Rx(θ)`. -/
def rotXMat (θ : TrigAngle R) : Mat3 R :=
  ⟨⟨ur, zr, zr⟩,
   ⟨zr, θ.c, θ.s⟩,
   ⟨zr, -ᵣθ.s, θ.c⟩⟩

private def cycPerm : SO3 R where
  mat := ⟨⟨zr, ur, zr⟩, ⟨zr, zr, ur⟩, ⟨ur, zr, zr⟩⟩
  mul_transpose := by
    simp [matMul, matTranspose, matId, vec3Dot, one_mul, zero_mul, add_zero, zero_add]
  transpose_mul := by
    simp [matMul, matTranspose, matId, vec3Dot, one_mul, zero_mul, add_zero, zero_add]
  det_one := by
    simp [matDet, vec3Dot, vecCross, ExactCommRing.sub, one_mul, zero_mul, add_zero, zero_add, neg_zero]
  preserves_cross := by
    intro u v
    simp [mxv, vecCross, vec3Dot, one_mul, zero_mul, add_zero, zero_add]

/-- Proof that `rotXMat θ` lies in `SO3 R` via conjugation `Pᵀ · Rz(θ) · P = Rx(θ)`. -/
def rotX (θ : TrigAngle R) : SO3 R :=
  let conj := SO3.comp cycPerm.inv (SO3.comp (rotZ θ) cycPerm)
  have hmat : conj.mat = rotXMat θ := by
    unfold conj SO3.comp SO3.inv cycPerm rotZ rotZMat rotXMat
    simp [matMul, matTranspose, vec3Dot, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  { mat := rotXMat θ
    mul_transpose := hmat ▸ conj.mul_transpose
    transpose_mul := hmat ▸ conj.transpose_mul
    det_one := hmat ▸ conj.det_one
    preserves_cross := hmat ▸ conj.preserves_cross }

/-- Angle negation `-θ`: `(cos(-θ), sin(-θ)) = (cos θ, -sin θ)`. -/
def negAngle (θ : TrigAngle R) : TrigAngle R where
  c := θ.c
  s := -ᵣθ.s
  unit := by rw [neg_mul_neg]; exact θ.unit

/-- Half-turn angle `θ + π`: `(cos(θ + π), sin(θ + π)) = (-cos θ, -sin θ)`. -/
def addPiAngle (θ : TrigAngle R) : TrigAngle R where
  c := -ᵣθ.c
  s := -ᵣθ.s
  unit := by rw [neg_mul_neg, neg_mul_neg]; exact θ.unit

-- ============================================================================
-- 3. `EARTHL`, `EARTHMX`, `MOONMX` & `MOONMXA` (PAGES 1143–1147)
-- ============================================================================

/-- `EARTHL` (`Page 1147`, lines 358–366): Earth polar-motion vector `L = (-AXO, -AYO, 0)`. -/
def earthL (axo negAyo : R) : Vec3 R :=
  ⟨-ᵣaxo, negAyo, zr⟩

/-- `EARTHMX` (`Page 1146`, lines 310–335): 3×3 Earth Z-rotation matrix `M(AZ) = Rz(AZ)`. -/
def earthMX (az : TrigAngle R) : Mat3 R :=
  rotZMat az

/-- `MOONMX` & `MOONMXA` (`Pages 1143–1145`, lines 161–255): intermediate vectors & matrix rows. -/
def moonAvectr (b nodi : TrigAngle R) : Vec3 R :=
  ⟨nodi.c, b.c *ᵣ nodi.s, b.s *ᵣ nodi.s⟩

def moonBvectr (b nodi : TrigAngle R) : Vec3 R :=
  ⟨-ᵣnodi.s, b.c *ᵣ nodi.c, b.s *ᵣ nodi.c⟩

def moonCvectr (b : TrigAngle R) : Vec3 R :=
  ⟨zr, -ᵣb.s, b.c⟩

def moonDvectr (b nodi incl : TrigAngle R) : Vec3 R :=
  vecSub (vecScale incl.c (moonBvectr b nodi)) (vecScale incl.s (moonCvectr b))

def moonM2 (b nodi incl : TrigAngle R) : Vec3 R :=
  vecAdd (vecScale incl.s (moonBvectr b nodi)) (vecScale incl.c (moonCvectr b))

def moonM1 (b f nodi incl : TrigAngle R) : Vec3 R :=
  vecSub (vecScale f.s (moonAvectr b nodi)) (vecScale f.c (moonDvectr b nodi incl))

def moonM0 (b f nodi incl : TrigAngle R) : Vec3 R :=
  vecNeg (vecAdd (vecScale f.c (moonAvectr b nodi)) (vecScale f.s (moonDvectr b nodi incl)))

/-- Final 3×3 Lunar Transformation Matrix `MMATRIX` constructed by `MOONMX` / `MOONMXA`. -/
def moonMX (b f nodi incl : TrigAngle R) : Mat3 R :=
  ⟨moonM0 b f nodi incl, moonM1 b f nodi incl, moonM2 b nodi incl⟩

/--
  Exact Euler-angle factorization theorem for Luminary 1A `MOONMX` (`Pages 1143–1145`):
  `MOONMX(B, F, NODI, I) = Rz(F + π) · Rx(-I) · Rz(NODI) · Rx(B)` identically!
-/
theorem moonMX_eq_euler_product (b f nodi incl : TrigAngle R) :
    moonMX b f nodi incl =
      matMul (rotZMat (addPiAngle f))
        (matMul (rotXMat (negAngle incl))
          (matMul (rotZMat nodi) (rotXMat b))) := by
  have hAB : matMul (rotZMat nodi) (rotXMat b) =
      ⟨moonAvectr b nodi, moonBvectr b nodi, moonCvectr b⟩ := by
    unfold matMul matTranspose rotZMat rotXMat moonAvectr moonBvectr moonCvectr vec3Dot
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
    congr 1
    · congr 1 <;> exact mul_comm _ _
    · congr 1 <;> exact mul_comm _ _
  rw [hAB]
  have hAD : matMul (rotXMat (negAngle incl)) ⟨moonAvectr b nodi, moonBvectr b nodi, moonCvectr b⟩ =
      ⟨moonAvectr b nodi, moonDvectr b nodi incl, moonM2 b nodi incl⟩ := by
    unfold matMul matTranspose rotXMat negAngle moonDvectr moonM2 vecSub vecAdd vecScale vec3Dot ExactCommRing.sub
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg]
  rw [hAD]
  unfold moonMX matMul matTranspose rotZMat addPiAngle moonM0 moonM1 vecNeg vecSub vecAdd vecScale vec3Dot ExactCommRing.sub
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg, neg_add]

def earthMX_SO3 (az : TrigAngle R) : SO3 R := rotZ az

def moonMX_SO3 (b f nodi incl : TrigAngle R) : SO3 R :=
  let prod := SO3.comp (rotZ (addPiAngle f))
                (SO3.comp (rotX (negAngle incl))
                  (SO3.comp (rotZ nodi) (rotX b)))
  have hmat : prod.mat = moonMX b f nodi incl :=
    (moonMX_eq_euler_product b f nodi incl).symm
  { mat := moonMX b f nodi incl
    mul_transpose := hmat ▸ prod.mul_transpose
    transpose_mul := hmat ▸ prod.transpose_mul
    det_one := hmat ▸ prod.det_one
    preserves_cross := hmat ▸ prod.preserves_cross }

-- ============================================================================
-- 4. `RP-TO-R` & `R-TO-RP` SUBROUTINES (PAGES 1140–1143)
-- ============================================================================

/-- Target body selector matching AGC `BHIZ` dispatch on `MPAC`:
    - `earth`: `MPAC = 0` (`RPTORA` / `RTORPA`)
    - `moon`:  `MPAC ≠ 0` (Lunar path) -/
inductive PlanetaryBody where
  | earth : PlanetaryBody
  | moon  : PlanetaryBody
  deriving Repr, DecidableEq

/-- Launch & ephemeris orientation parameters at epoch `T`. -/
structure OrientationParams (R : Type) [ExactCommRing R] where
  earthAz     : TrigAngle R  -- `AZ(T)` from `NEWANGLE` (`EARTHMX`)
  earthAxo    : R            -- `AXO` (`EARTHL`)
  earthNegAyo : R            -- `-AYO` (`EARTHL`)
  moonB       : TrigAngle R  -- `B(T)` (`MOONMX`)
  moonF       : TrigAngle R  -- `F(T)` (`MOONMX`)
  moonNodi    : TrigAngle R  -- `NODI(T)` (`MOONMX`)
  moonIncl    : TrigAngle R  -- Lunar inclination `I` (`COSI, SINI`)
  moonLM      : Vec3 R       -- `504LM`: Moon libration vector `LP` in Moon-fixed frame

/-- Computable transformation matrix `M(T)` for the selected body (no proof terms in data). -/
def bodyMatrix (body : PlanetaryBody) (p : OrientationParams R) : Mat3 R :=
  match body with
  | .earth => earthMX p.earthAz
  | .moon  => moonMX p.moonB p.moonF p.moonNodi p.moonIncl

/-- Packaged `SO(3)` proof for `bodyMatrix`. -/
def bodyMatrixSO3 (body : PlanetaryBody) (p : OrientationParams R) : SO3 R :=
  match body with
  | .earth => earthMX_SO3 p.earthAz
  | .moon  => moonMX_SO3 p.moonB p.moonF p.moonNodi p.moonIncl

theorem bodyMatrixSO3_mat (body : PlanetaryBody) (p : OrientationParams R) :
    (bodyMatrixSO3 body p).mat = bodyMatrix body p := by
  cases body <;> rfl

/-- Inertial libration / polar-motion vector `L` (used in `R-TO-RP`). -/
def bodyLInertial (body : PlanetaryBody) (p : OrientationParams R) : Vec3 R :=
  match body with
  | .earth => earthL p.earthAxo p.earthNegAyo
  | .moon  => vxm p.moonLM (bodyMatrix .moon p)

/-- Planetary-fixed libration / polar-motion vector `LP` (used in `RP-TO-R`). -/
def bodyLPlanetary (body : PlanetaryBody) (p : OrientationParams R) : Vec3 R :=
  match body with
  | .earth => mxv (bodyMatrix .earth p) (earthL p.earthAxo p.earthNegAyo)
  | .moon  => p.moonLM

/-- `RP-TO-R` (`Pages 1140–1141`): `R = M(T)ᵀ · (RP + LP × RP)`. -/
def rpToR (body : PlanetaryBody) (p : OrientationParams R) (rp : Vec3 R) : Vec3 R :=
  let m := bodyMatrix body p
  let lp := bodyLPlanetary body p
  vxm (vecAdd rp (vecCross lp rp)) m

/-- `R-TO-RP` (`Pages 1142–1143`): `RP = M(T) · (R - L × R)`. -/
def rToRp (body : PlanetaryBody) (p : OrientationParams R) (r : Vec3 R) : Vec3 R :=
  let m := bodyMatrix body p
  let l := bodyLInertial body p
  mxv m (vecSub r (vecCross l r))

-- ============================================================================
-- 5. KERNEL-VERIFIED `SO(3)` & FRAME TRANSFORMATION THEOREMS
-- ============================================================================

/-- Universal theorem: `EARTHMX(AZ)` is orthogonal (`M · Mᵀ = I₃`, `Mᵀ · M = I₃`) with `det = 1`. -/
theorem earthMX_is_SO3 (az : TrigAngle R) :
    matMul (earthMX az) (matTranspose (earthMX az)) = matId ∧
    matMul (matTranspose (earthMX az)) (earthMX az) = matId ∧
    matDet (earthMX az) = ur :=
  ⟨(earthMX_SO3 az).mul_transpose, (earthMX_SO3 az).transpose_mul, (earthMX_SO3 az).det_one⟩

/-- Universal theorem: Luminary 1A `MOONMX(B, F, NODI, I)` is an exact proper orthogonal
    rotation matrix (`M · Mᵀ = I₃`, `Mᵀ · M = I₃`, `det(M) = 1`) for ALL angles over ANY ring `R`. -/
theorem moonMX_is_SO3 (b f nodi incl : TrigAngle R) :
    matMul (moonMX b f nodi incl) (matTranspose (moonMX b f nodi incl)) = matId ∧
    matMul (matTranspose (moonMX b f nodi incl)) (moonMX b f nodi incl) = matId ∧
    matDet (moonMX b f nodi incl) = ur :=
  ⟨(moonMX_SO3 b f nodi incl).mul_transpose,
   (moonMX_SO3 b f nodi incl).transpose_mul,
   (moonMX_SO3 b f nodi incl).det_one⟩

/-- Exact relation between planetary-fixed `LP` and inertial `L` for BOTH Earth and Moon:
    `LP = M · L` and `L = Mᵀ · LP`. -/
theorem bodyL_conversion (body : PlanetaryBody) (p : OrientationParams R) :
    mxv (bodyMatrix body p) (bodyLInertial body p) = bodyLPlanetary body p ∧
    vxm (bodyLPlanetary body p) (bodyMatrix body p) = bodyLInertial body p := by
  cases body
  · constructor
    · rfl
    · exact (earthMX_SO3 p.earthAz).vxm_mxv (earthL p.earthAxo p.earthNegAyo)
  · constructor
    · exact (moonMX_SO3 p.moonB p.moonF p.moonNodi p.moonIncl).mxv_vxm p.moonLM
    · rfl

/--
  Universal exact second-order libration cancellation theorem (`R-TO-RP ∘ RP-TO-R`):
  For BOTH Earth and Moon and ANY libration / polar-motion vector `LP`, the first-order
  terms `+LP × RP` and `-LP × RP` CANCEL IDENTICALLY:
  `R-TO-RP(RP-TO-R(rp)) = rp - LP × (LP × rp)`.
-/
theorem rToRp_rpToR_second_order_residual (body : PlanetaryBody) (p : OrientationParams R) (rp : Vec3 R) :
    rToRp body p (rpToR body p rp) =
      vecSub rp (vecCross (bodyLPlanetary body p) (vecCross (bodyLPlanetary body p) rp)) := by
  unfold rToRp rpToR
  let M := bodyMatrixSO3 body p
  have hM : bodyMatrix body p = M.mat := (bodyMatrixSO3_mat body p).symm
  rw [hM]
  have hML : mxv M.mat (bodyLInertial body p) = bodyLPlanetary body p := by
    rw [← hM]; exact (bodyL_conversion body p).1
  rw [mxv_sub, M.preserves_cross, hML, M.mxv_vxm, vecCross_add_right]
  unfold vecSub vecAdd ExactCommRing.sub
  have hcancel (a b c : R) : (a +ᵣ b) +ᵣ -ᵣ(b +ᵣ c) = a +ᵣ -ᵣc := by
    rw [neg_add, add_assoc, ← add_assoc b (-ᵣb), add_right_neg, zero_add]
  congr 1 <;> apply hcancel

/--
  Universal exact second-order libration cancellation theorem (`RP-TO-R ∘ R-TO-RP`):
  For BOTH Earth and Moon and ANY libration / polar-motion vector `L`:
  `RP-TO-R(R-TO-RP(r)) = r - L × (L × r)`.
-/
theorem rpToR_rToRp_second_order_residual (body : PlanetaryBody) (p : OrientationParams R) (r : Vec3 R) :
    rpToR body p (rToRp body p r) =
      vecSub r (vecCross (bodyLInertial body p) (vecCross (bodyLInertial body p) r)) := by
  unfold rpToR rToRp
  let M := bodyMatrixSO3 body p
  have hM : bodyMatrix body p = M.mat := (bodyMatrixSO3_mat body p).symm
  rw [hM]
  have hMtLP : vxm (bodyLPlanetary body p) M.mat = bodyLInertial body p := by
    rw [← hM]; exact (bodyL_conversion body p).2
  have hinv := M.inv.preserves_cross (bodyLPlanetary body p) (mxv M.mat (vecSub r (vecCross (bodyLInertial body p) r)))
  unfold vxm
  rw [mxv_add]
  have hcr : mxv (matTranspose M.mat)
      (vecCross (bodyLPlanetary body p) (mxv M.mat (vecSub r (vecCross (bodyLInertial body p) r)))) =
      vecCross (vxm (bodyLPlanetary body p) M.mat)
               (vxm (mxv M.mat (vecSub r (vecCross (bodyLInertial body p) r))) M.mat) := hinv
  rw [hcr, hMtLP, M.vxm_mxv]
  have h1 : mxv (matTranspose M.mat) (mxv M.mat (vecSub r (vecCross (bodyLInertial body p) r))) =
      vecSub r (vecCross (bodyLInertial body p) r) := M.vxm_mxv _
  rw [h1, vecCross_sub_right]
  unfold vecAdd vecSub ExactCommRing.sub
  have hcancel (a b c : R) : (a +ᵣ -ᵣb) +ᵣ (b +ᵣ -ᵣc) = a +ᵣ -ᵣc := by
    rw [add_assoc, ← add_assoc (-ᵣb) b, add_left_neg, zero_add]
  congr 1 <;> apply hcancel

/--
  Universal exact inverse theorems when libration / polar-motion is zero:
  `R-TO-RP(RP-TO-R(rp)) = rp` and `RP-TO-R(R-TO-RP(r)) = r` identically!
-/
theorem rToRp_rpToR_exact_inverse_zero_libration (body : PlanetaryBody) (p : OrientationParams R)
    (hL : bodyLPlanetary body p = vecZero) (rp : Vec3 R) :
    rToRp body p (rpToR body p rp) = rp := by
  rw [rToRp_rpToR_second_order_residual, hL, vecCross_zero_left, vecSub_zero]

theorem rpToR_rToRp_exact_inverse_zero_libration (body : PlanetaryBody) (p : OrientationParams R)
    (hL : bodyLInertial body p = vecZero) (r : Vec3 R) :
    rpToR body p (rToRp body p r) = r := by
  rw [rpToR_rToRp_second_order_residual, hL, vecCross_zero_left, vecSub_zero]

/--
  Universal exact Pythagorean norm theorem for `RP-TO-R`:
  Because `Mᵀ ∈ SO(3)` preserves norms and `rp ⊥ (LP × rp)`,
  `‖RP-TO-R(rp)‖² = ‖rp‖² + ‖LP × rp‖²` identically!
-/
theorem rpToR_norm_sq_exact (body : PlanetaryBody) (p : OrientationParams R) (rp : Vec3 R) :
    vec3NormSq (rpToR body p rp) =
      vec3NormSq rp +ᵣ vec3NormSq (vecCross (bodyLPlanetary body p) rp) := by
  unfold rpToR
  let M := bodyMatrixSO3 body p
  have hM : bodyMatrix body p = M.mat := (bodyMatrixSO3_mat body p).symm
  rw [hM]
  change vec3NormSq (mxv M.inv.mat (vecAdd rp (vecCross (bodyLPlanetary body p) rp))) = _
  rw [M.inv.preserves_norm_sq]
  have hnorm_add (a b : Vec3 R) :
      vec3NormSq (vecAdd a b) =
        (vec3NormSq a +ᵣ vec3NormSq b) +ᵣ (vec3Dot a b +ᵣ vec3Dot a b) := by
    unfold vec3NormSq vec3Dot vecAdd
    have hsq (x y : R) : (x +ᵣ y) *ᵣ (x +ᵣ y) = (x *ᵣ x +ᵣ y *ᵣ y) +ᵣ (x *ᵣ y +ᵣ x *ᵣ y) := by
      rw [left_distrib, right_distrib, right_distrib, mul_comm y x,
          add4_rearrange (x *ᵣ x) (x *ᵣ y) (x *ᵣ y) (y *ᵣ y),
          add_comm (x *ᵣ y) (y *ᵣ y),
          add4_rearrange (x *ᵣ x) (x *ᵣ y) (y *ᵣ y) (x *ᵣ y)]
    rw [hsq a.x b.x, hsq a.y b.y, hsq a.z b.z]
    have hgroup (A1 B1 C1 A2 B2 C2 A3 B3 C3 : R) :
        (((A1 +ᵣ B1) +ᵣ (C1 +ᵣ C1)) +ᵣ ((A2 +ᵣ B2) +ᵣ (C2 +ᵣ C2))) +ᵣ ((A3 +ᵣ B3) +ᵣ (C3 +ᵣ C3)) =
        (((A1 +ᵣ A2) +ᵣ A3) +ᵣ ((B1 +ᵣ B2) +ᵣ B3)) +ᵣ (((C1 +ᵣ C2) +ᵣ C3) +ᵣ ((C1 +ᵣ C2) +ᵣ C3)) := by
      rw [add4_rearrange (A1 +ᵣ B1) (C1 +ᵣ C1) (A2 +ᵣ B2) (C2 +ᵣ C2)]
      rw [add4_rearrange A1 B1 A2 B2, add4_rearrange C1 C1 C2 C2]
      rw [add4_rearrange ((A1 +ᵣ A2) +ᵣ (B1 +ᵣ B2)) ((C1 +ᵣ C2) +ᵣ (C1 +ᵣ C2)) (A3 +ᵣ B3) (C3 +ᵣ C3)]
      rw [add4_rearrange (A1 +ᵣ A2) (B1 +ᵣ B2) A3 B3, add4_rearrange (C1 +ᵣ C2) (C1 +ᵣ C2) C3 C3]
    exact hgroup _ _ _ _ _ _ _ _ _
  rw [hnorm_add, vec3Dot_cross_right_self rp (bodyLPlanetary body p), add_zero, add_zero]

end RingLinearAlgebra

-- ============================================================================
-- 6. `NEWANGLE` — EXACT TRIPLE-PRECISION TIME & ANGLE PROPAGATION (PAGE 1145)
-- ============================================================================

def newangleShiftLo (x1 : Nat) : Nat := 5 - x1
def newangleShiftHi (x1 : Nat) : Nat := 10 - x1

/--
  Exact AGC `NEWANGLE` triple-precision split computation (`Page 1145`, lines 264–284):
  - `part1 = x0 + (tLo * xdot) * 2^(5 - x1)`         (`DMP; SL* 5,1; DAD`)
  - `part2 = ((tHi * 2^9) * xdot) * 2^(10 - x1)`     (`SLOAD TIMSUBM; SL 9D; DMP 10D; SL* 10D,1`)
  - `result = part1 + part2`                         (`DAD`)
-/
def newangleSplit (x0 xdot tHi tLo : Int) (x1 : Nat) : Int :=
  let part1 := x0 + (tLo * xdot) * (2 ^ (newangleShiftLo x1) : Int)
  let part2 := ((tHi * (2 ^ 9 : Int)) * xdot) * (2 ^ (newangleShiftHi x1) : Int)
  part1 + part2

/-- Unified (unsplit) exact mathematical formula `X = X0 + (tHi · 2^14 + tLo) · XDOT · 2^(5 - x1)`. -/
def newangleUnified (x0 xdot tHi tLo : Int) (x1 : Nat) : Int :=
  x0 + ((tHi * (2 ^ 14 : Int) + tLo) * xdot) * (2 ^ (newangleShiftLo x1) : Int)

private theorem int_pow_add (a : Int) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp [Int.pow_zero, Int.mul_one]
  | succ k ih =>
    rw [Nat.add_succ, Int.pow_succ, Int.pow_succ, ih, Int.mul_assoc]

/--
  Universal exact theorem (`PLANETARY_INERTIAL_ORIENTATION.agc`, Page 1145):
  For ALL integers `x0, xdot, tHi, tLo` and ALL `x1 ≤ 5` (covering Earth `WEARTH = 0`,
  Moon `FDOT = 4`, Moon `BDOT/NODDOT = 5`), the AGC triple-precision split multiplication
  is **ALGEBRAICALLY IDENTICAL** to the unsplit product `X0 + (tHi · 2^14 + tLo) · XDOT · 2^(5 - x1)`.
-/
theorem newangle_tp_split_exact (x0 xdot tHi tLo : Int) (x1 : Nat) (hx1 : x1 ≤ 5) :
    newangleSplit x0 xdot tHi tLo x1 = newangleUnified x0 xdot tHi tLo x1 := by
  unfold newangleSplit newangleUnified newangleShiftLo newangleShiftHi
  have hexp : (2 ^ 9 : Int) * (2 ^ (10 - x1) : Int) = (2 ^ 14 : Int) * (2 ^ (5 - x1) : Int) := by
    rw [← int_pow_add, ← int_pow_add]
    congr 1
    omega
  calc
    (x0 + (tLo * xdot) * (2 ^ (5 - x1) : Int)) +
      ((tHi * (2 ^ 9 : Int)) * xdot) * (2 ^ (10 - x1) : Int)
      = x0 + ((tLo * xdot) * (2 ^ (5 - x1) : Int) +
          tHi * xdot * ((2 ^ 9 : Int) * (2 ^ (10 - x1) : Int))) := by
        rw [Int.add_assoc]
        congr 1; congr 1
        rw [Int.mul_assoc tHi (2 ^ 9 : Int) xdot, Int.mul_comm (2 ^ 9 : Int) xdot,
            ← Int.mul_assoc tHi xdot (2 ^ 9 : Int), Int.mul_assoc]
    _ = x0 + ((tLo * xdot) * (2 ^ (5 - x1) : Int) +
          tHi * xdot * ((2 ^ 14 : Int) * (2 ^ (5 - x1) : Int))) := by
        rw [hexp]
    _ = x0 + ((tHi * (2 ^ 14 : Int) + tLo) * xdot) * (2 ^ (5 - x1) : Int) := by
        congr 1
        have h1 : tHi * xdot * ((2 ^ 14 : Int) * (2 ^ (5 - x1) : Int)) =
            (tHi * (2 ^ 14 : Int) * xdot) * (2 ^ (5 - x1) : Int) := by
          rw [← Int.mul_assoc, Int.mul_assoc tHi xdot (2 ^ 14 : Int),
              Int.mul_comm xdot (2 ^ 14 : Int), ← Int.mul_assoc]
        rw [h1, Int.add_comm ((tLo * xdot) * (2 ^ (5 - x1) : Int)), ← Int.add_mul, ← Int.add_mul]

/-- Exact Luminary 1A `NEWANGLE` shift schedule verification (`Pages 1143–1146`). -/
theorem newangle_shift_table_luminary :
    (newangleShiftLo 0, newangleShiftHi 0) = (5, 10) ∧  -- EARTHMX: WEARTH
    (newangleShiftLo 4, newangleShiftHi 4) = (1, 6)  ∧  -- MOONMX:  FDOT
    (newangleShiftLo 5, newangleShiftHi 5) = (0, 5) := by -- MOONMX:  BDOT / NODDOT
  decide

/-- Exact `T >> 14 + TIMSUBO` binary-point alignment from B-28 (`T`) to B-42 (`TIMSUBO`): `28 + 14 = 42`. -/
theorem newangle_time_alignment : (28 : Nat) + 14 = 42 := rfl

-- ============================================================================
-- 7. CONCRETE EXECUTABLE VERIFICATION SUITE (`decide`)
-- ============================================================================

def ang0   : TrigAngle Int := ⟨1, 0, by decide⟩
def ang90  : TrigAngle Int := ⟨0, 1, by decide⟩
def ang180 : TrigAngle Int := ⟨-1, 0, by decide⟩

/-- Concrete verification of `EARTHMX(90°)` and `MOONMX(0°, 90°, 90°, 0°)` in `Int`. -/
theorem verify_earth_and_moon_cardinal_frames :
    let p : OrientationParams Int :=
      { earthAz := ang90, earthAxo := 0, earthNegAyo := 0,
        moonB := ang0, moonF := ang90, moonNodi := ang90, moonIncl := ang0,
        moonLM := ⟨0, 0, 0⟩ }
    rpToR .earth p ⟨10, 20, 30⟩ = ⟨-20, 10, 30⟩ ∧
    rToRp .earth p (rpToR .earth p ⟨10, 20, 30⟩) = ⟨10, 20, 30⟩ ∧
    rToRp .moon p (rpToR .moon p ⟨1737400, -50000, 12345⟩) = ⟨1737400, -50000, 12345⟩ := by
  decide

end ApolloMission.PlanetaryInertialOrientation
