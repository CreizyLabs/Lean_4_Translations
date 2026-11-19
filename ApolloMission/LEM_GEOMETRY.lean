/-!
# Apollo 11 Luminary 1A (Build 099) — `LEM_GEOMETRY.agc` Formalization in Lean 4

Primary archival source:
- MIT Instrumentation Laboratory, *Luminary 1A (Rev. 001, Build 099, NASA 2021112-061)*,
  `LEM_GEOMETRY.agc`, Pages 320–325 (16:27 July 14, 1969).

Formalized routines:
1. `SVDWN2` (Page 320): Actual state vector downlink computation (`RN`, `VN`, `PIPTIME`)
   guarded by `AVEMIDSW` with `X2`-indexed `VSL*` scaling (B-27/B-5 lunar vs. B-29/B-7 earth).
2. `SVDWN1` (Page 321): Other-vehicle state vector computation (`R-OTHER`, `V-OTHER`).
3. `RRANGLES` (Pages 322–323): Rendezvous Radar (RR) Mode 1 & Mode 2 gimbal angle solver,
   Y-axis gimbal-lock detection (`BOVB LUNDESCH`), 1's-to-2's complement CDU conversion
   (`2V1STO2S`), and Basic AGC `RADMODES`/`ANTENBIT` 3-instruction `DXCH` swap.
4. `RRNB` & `RRNBMPAC` (Page 324): Rendezvous Radar forward kinematics from CDU `(T, S)`
   via `CDULOGIC` to the half-unit line-of-sight vector in Navigation Base axes:
   `0.5 * (sin(S)cos(T), -sin(T), cos(S)cos(T))`.

Verification guarantees:
- Zero `sorry`
- Zero custom `axiom`s
- Zero floating-point approximations (exact `BitVec 15`, exact `Int` scaling, and
  universal exact commutative-ring algebraic geometry proofs)
-/

namespace ApolloMission.LEMGeometry

-- ============================================================================
-- 1. EXACT COMMUTATIVE RING & EXACT ALGEBRAIC TRIGONOMETRY (ZERO AXIOMS)
-- ============================================================================

/-- Constructive commutative ring typeclass with zero custom axioms. -/
class ExactCommRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  zero_add : ∀ a : R, add zero a = a
  add_zero : ∀ a : R, add a zero = a
  add_comm : ∀ a b : R, add a b = add b a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : R, mul one a = a
  mul_one : ∀ a : R, mul a one = a
  mul_comm : ∀ a b : R, mul a b = mul b a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

namespace ExactCommRing

def sub {R : Type} [ExactCommRing R] (a b : R) : R :=
  add a (neg b)

theorem add_right_neg {R : Type} [ExactCommRing R] (a : R) :
    add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem zero_mul {R : Type} [ExactCommRing R] (a : R) :
    mul zero a = zero := by
  have h1 : add (mul zero a) (mul zero a) = mul zero a := by
    rw [← right_distrib, zero_add]
  have h2 : add (neg (mul zero a)) (add (mul zero a) (mul zero a)) =
      add (neg (mul zero a)) (mul zero a) := congrArg (add (neg (mul zero a))) h1
  rw [← add_assoc, add_left_neg, zero_add] at h2
  exact h2

theorem mul_zero {R : Type} [ExactCommRing R] (a : R) :
    mul a zero = zero := by
  rw [mul_comm, zero_mul]

theorem neg_unique {R : Type} [ExactCommRing R] (a b : R) (h : add a b = zero) :
    b = neg a := by
  have h1 := congrArg (add (neg a)) h
  rw [← add_assoc, add_left_neg, zero_add, add_zero] at h1
  exact h1

theorem neg_neg {R : Type} [ExactCommRing R] (a : R) :
    neg (neg a) = a := by
  symm
  exact neg_unique (neg a) a (add_left_neg a)

theorem neg_zero {R : Type} [ExactCommRing R] :
    neg (zero : R) = zero := by
  symm
  exact neg_unique zero zero (zero_add zero)

theorem neg_mul {R : Type} [ExactCommRing R] (a b : R) :
    mul (neg a) b = neg (mul a b) := by
  apply neg_unique (mul a b) (mul (neg a) b)
  rw [← right_distrib, add_right_neg, zero_mul]

theorem mul_neg {R : Type} [ExactCommRing R] (a b : R) :
    mul a (neg b) = neg (mul a b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg {R : Type} [ExactCommRing R] (a b : R) :
    mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_add {R : Type} [ExactCommRing R] (a b : R) :
    neg (add a b) = add (neg a) (neg b) := by
  symm
  apply neg_unique (add a b) (add (neg a) (neg b))
  calc
    add (add a b) (add (neg a) (neg b))
      = add a (add b (add (neg a) (neg b))) := add_assoc _ _ _
    _ = add a (add b (add (neg b) (neg a))) := by rw [add_comm (neg a) (neg b)]
    _ = add a (add (add b (neg b)) (neg a)) := by rw [← add_assoc b (neg b) (neg a)]
    _ = add a (add zero (neg a)) := by rw [add_right_neg]
    _ = add a (neg a) := by rw [zero_add]
    _ = zero := add_right_neg a

end ExactCommRing

/-- Exact `Int` instance of `ExactCommRing`. -/
instance : ExactCommRing Int where
  zero := 0
  one := 1
  add := Int.add
  neg := Int.neg
  mul := Int.mul
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_comm := Int.add_comm
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

/-- Exact trigonometric angle `(cos θ, sin θ)` on the unit circle `c² + s² = 1`. -/
structure TrigAngle (R : Type) [ExactCommRing R] where
  c : R
  s : R
  unit : ExactCommRing.add (ExactCommRing.mul c c) (ExactCommRing.mul s s) = ExactCommRing.one

/-- Exact 3-dimensional vector over any type `α`. -/
structure Vec3 (α : Type) where
  x : α
  y : α
  z : α
  deriving Repr, DecidableEq

/-- Componentwise addition of `Vec3 Int`. -/
@[inline] def vec3AddInt (u v : Vec3 Int) : Vec3 Int :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Exact dot product over `ExactCommRing R`. -/
def vec3Dot {R : Type} [ExactCommRing R] (u v : Vec3 R) : R :=
  ExactCommRing.add
    (ExactCommRing.add (ExactCommRing.mul u.x v.x) (ExactCommRing.mul u.y v.y))
    (ExactCommRing.mul u.z v.z)

/-- Exact squared Euclidean norm `‖u‖² = u · u` over `ExactCommRing R`. -/
def vec3NormSq {R : Type} [ExactCommRing R] (u : Vec3 R) : R :=
  vec3Dot u u

-- ============================================================================
-- 2. AGC BLOCK II 15-BIT HARDWARE PRIMITIVES & CDU CONVERSIONS
-- ============================================================================

abbrev Word15 := BitVec 15

def POS_ZERO : Word15 := 0o00000#15
def NEG_ZERO : Word15 := 0o77777#15
def POSMAX   : Word15 := 0o37777#15
def NEGMAX   : Word15 := 0o40000#15
def HALF_REV : Word15 := 0o20000#15  -- +0.5 rev (180 deg) scaled B-0 (`LODPHALF` major word)

/-- `ANTENBIT` in `RADMODES` (Luminary 1A): bit 12 (`0o04000`) indicates RR Mode 2 when set. -/
def ANTENBIT : Word15 := 0o04000#15

/-- 15-bit ones'-complement negation (`CS` / `COM`). -/
@[inline] def comp15 (w : Word15) : Word15 := ~~~w

/-- 15-bit ones'-complement addition with end-around carry. -/
@[inline] def add15 (x y : Word15) : Word15 :=
  let s : Nat := x.toNat + y.toNat
  let s' : Nat := if s > 0o77777 then (s &&& 0o77777) + 1 else s
  BitVec.ofNat 15 (s' &&& 0o77777)

/-- 15-bit AGC `CCS` (Count, Compare, and Skip) evaluation. -/
@[inline] def ccsEval (w : Word15) : Nat × Word15 :=
  if w == POS_ZERO then (1, POS_ZERO)
  else if w == NEG_ZERO then (3, POS_ZERO)
  else if (w &&& 0o40000#15) == 0#15 then
    (0, BitVec.ofNat 15 ((w.toNat - 1) &&& 0o77777))
  else
    let mag := comp15 w
    (2, BitVec.ofNat 15 ((mag.toNat - 1) &&& 0o77777))

/--
  AGC `1STO2S` / `2V1STO2S` (Single/Pair 1's Complement to 2's Complement CDU Conversion):
  Converts a 15-bit ones'-complement angle to a 15-bit two's-complement CDU angle.
  - Non-negative (`bit 15 == 0`): unchanged.
  - Negative (`bit 15 == 1`): add 1 mod `2^15` (maps `-0 = 0o77777` to `+0 = 0o00000`).
-/
@[inline] def onesToTwos15 (w : Word15) : Word15 :=
  if (w &&& 0o40000#15) == 0#15 then w else w + 1#15

/--
  AGC `CDULOGIC` (2's Complement CDU to 1's Complement Conversion):
  Converts a 15-bit two's-complement CDU angle back to 15-bit ones'-complement.
  - Non-negative (`bit 15 == 0`): unchanged.
  - Strictly negative in `0o40001..0o77777`: subtract 1 (restoring 1's complement sign-magnitude).
  - Extreme `-180°` (`0o40000`): maps to `NEGMAX` (`0o40000` in 1's complement, `-16383`).
-/
@[inline] def cduLogicToOnes15 (cdu : Word15) : Word15 :=
  if (cdu &&& 0o40000#15) == 0#15 then cdu
  else if cdu == 0o40000#15 then NEGMAX
  else cdu - 1#15

/-- Pairwise `2V1STO2S` converting `(Trunnion, Shaft)` to 2's-complement CDU pair. -/
@[inline] def twoV1sTo2s (ts : Word15 × Word15) : Word15 × Word15 :=
  (onesToTwos15 ts.1, onesToTwos15 ts.2)

/--
  Exact AGC binary scaling shift (truncating toward zero for right shifts, matching
  ones'-complement sign-magnitude shifting in the AGC Interpreter `VSL*` / `VSR`).
  - `k ≥ 0`: multiply by `2^k` (`VSL`)
  - `k < 0`: truncated division by `2^(-k)` (`VSR`, preserving sign symmetry `shift (-x) k = - shift x k`)
-/
def agcShiftInt (v : Int) (k : Int) : Int :=
  if k ≥ 0 then
    v * (2 ^ k.toNat : Int)
  else
    let d : Int := (2 ^ (-k).toNat : Int)
    Int.tdiv v d

/-- Componentwise AGC vector shift (`VSL*`). -/
@[inline] def agcShiftVec (v : Vec3 Int) (k : Int) : Vec3 Int :=
  ⟨agcShiftInt v.x k, agcShiftInt v.y k, agcShiftInt v.z k⟩

-- ============================================================================
-- 3. `SVDWN2` & `SVDWN1` — STATE VECTOR DOWNLINK ROUTINES (PAGES 320–321)
-- ============================================================================

/--
  Erasable & Interpretive state relevant to `SVDWN2` and `SVDWN1` (`LEM_GEOMETRY.agc`, pp. 320–321).
  - `x2 = 0`: input state vector scaled pos B-29, vel B-7 (Earth)
  - `x2 = 2`: input state vector scaled pos B-27, vel B-5 (Moon)
  - Output `rn`/`rOther` is ALWAYS meters B-29; `vn`/`vOther` is ALWAYS meters/csec B-7.
-/
structure DownlinkState where
  avemidsw : Bool      -- `AVEMIDSW`: 1 = AVETOMID doing W-matrix integration
  x2       : Int       -- Index register `X2` (`0` for B-29/B-7, `2` for B-27/B-5)
  tdeltav  : Vec3 Int  -- Position deviation `TDELTAV` (B-22 Earth / B-18 Moon)
  rcv      : Vec3 Int  -- Conic position `RCV` (B-29 Earth / B-27 Moon)
  tnuv     : Vec3 Int  -- Velocity deviation `TNUV` (B-3 Earth / B-1 Moon)
  vcv      : Vec3 Int  -- Conic velocity `VCV` (B-7 Earth / B-5 Moon)
  tet      : Int       -- Integration epoch time `TET`
  rn       : Vec3 Int  -- Output LM position `RN` (B-29)
  vn       : Vec3 Int  -- Output LM velocity `VN` (B-7)
  piptime  : Int       -- Output epoch `PIPTIME`
  rOther   : Vec3 Int  -- Output other-vehicle position `R-OTHER` (B-29)
  vOther   : Vec3 Int  -- Output other-vehicle velocity `V-OTHER` (B-7)
  deriving Repr, DecidableEq

/--
  Core AGC `SVDWN` state vector formula (lines 59–71 and 77–90):
  - `VLOAD TDELTAV; VSL* (0 - 7, 2); VAD RCV; VSL* (0, 2)`
    Note: AGC Interpreter indexing subtracts `C(X2)` from the shift operand:
    - `0 - 7, 2` => shift left by `-7 - X2` (right by `7` for `X2=0`, right by `9` for `X2=2`)
    - `0, 2`     => shift left by `0 - X2`  (right by `0` for `X2=0`, right by `2` for `X2=2`)
  - `VLOAD TNUV; VSL* (0 - 4, 2); VAD VCV; VSL* (0, 2)`
    - `0 - 4, 2` => shift left by `-4 - X2` (right by `4` for `X2=0`, right by `6` for `X2=2`)
    - `0, 2`     => shift left by `0 - X2`  (right by `0` for `X2=0`, right by `2` for `X2=2`)
-/
def computeDownlinkRV (st : DownlinkState) : Vec3 Int × Vec3 Int :=
  let rSum := vec3AddInt (agcShiftVec st.tdeltav (-7 - st.x2)) st.rcv
  let rOut := agcShiftVec rSum (-st.x2)
  let vSum := vec3AddInt (agcShiftVec st.tnuv (-4 - st.x2)) st.vcv
  let vOut := agcShiftVec vSum (-st.x2)
  (rOut, vOut)

/--
  `SVDWN2` (`LEM_GEOMETRY.agc`, Page 320, lines 56–75):
  Guarded by `BOF AVEMIDSW +1 / RVQ`. When `AVEMIDSW` is set, stores `(R(T), V(T), TET)`
  into `(RN, VN, PIPTIME)`.
-/
def svdwn2 (st : DownlinkState) : DownlinkState :=
  if !st.avemidsw then
    st
  else
    let (rOut, vOut) := computeDownlinkRV st
    { st with rn := rOut, vn := vOut, piptime := st.tet }

/--
  `SVDWN1` (`LEM_GEOMETRY.agc`, Page 321, lines 77–91):
  Unconditionally computes `(R(T), V(T))` and stores them into `(R-OTHER, V-OTHER)`.
-/
def svdwn1 (st : DownlinkState) : DownlinkState :=
  let (rOut, vOut) := computeDownlinkRV st
  { st with rOther := rOut, vOther := vOut }

-- ============================================================================
-- 4. `RRANGLES` — RENDEZVOUS RADAR GIMBAL ANGLE SOLVER (PAGES 322–323)
-- ============================================================================

/--
  Basic AGC assembly 3-instruction `DXCH` swap (`LEM_GEOMETRY.agc`, Page 323, lines 149–151):
  ```
    DXCH MODEA    -- (A,L) <-> MODEA
    DXCH MODEB    -- (A,L) <-> MODEB
    DXCH MODEA    -- (A,L) <-> MODEA
  ```
  Modeled faithfully with explicit `(A, L)` double-word register pair.
-/
def dxchSwap (al modeA modeB : Word15 × Word15) : (Word15 × Word15) × (Word15 × Word15) × (Word15 × Word15) :=
  let (al1, modeA1) := (modeA, al)       -- DXCH MODEA
  let (al2, modeB1) := (modeB, al1)      -- DXCH MODEB
  let (al3, modeA2) := (modeA1, al2)     -- DXCH MODEA
  (al3, modeA2, modeB1)

/--
  Basic AGC `RADMODES` / `ANTENBIT` swap logic (`LEM_GEOMETRY.agc`, Page 323, lines 144–152):
  ```
    CS   RADMODES   -- A := ~RADMODES
    MASK ANTENBIT   -- A := (~RADMODES) & ANTENBIT
    CCS  A          -- if A > +0 (i.e. ANTENBIT was 0 => Mode 1), branch to TCF +4 (skip swap)
    TCF  +4         -- skip swap
    DXCH MODEA      -- else (ANTENBIT was 1 => Mode 2), swap MODEA and MODEB
    DXCH MODEB
    DXCH MODEA
  ```
-/
def rrangleModeSwap (radmodes : Word15) (al mode1CDU mode2CDU : Word15 × Word15) :
    (Word15 × Word15) × (Word15 × Word15) :=
  let a := (comp15 radmodes) &&& ANTENBIT
  let (branch, _) := ccsEval a
  if branch == 0 then
    -- A > +0 => ANTENBIT clear => RR in Mode 1 => keep MODEA = Mode 1, MODEB = Mode 2
    (mode1CDU, mode2CDU)
  else
    -- A == +0 => ANTENBIT set => RR in Mode 2 => swap via 3-step DXCH
    let (_, modeA', modeB') := dxchSwap al mode1CDU mode2CDU
    (modeA', modeB')

/--
  Result of `RRANGLES` execution (`LEM_GEOMETRY.agc`, Pages 322–323):
  - `gimbalLock` (`BOVB LUNDESCH`): target vector lies along the Y-axis (`ux = 0 ∧ uz = 0`).
  - `angles modeA modeB`: 2's-complement CDU angle pairs `(Trunnion, Shaft)` for current mode
    (`MODEA`) and alternate remode (`MODEB`).
-/
inductive RRAnglesResult where
  | gimbalLock : RRAnglesResult
  | angles (modeA modeB : Word15 × Word15) : RRAnglesResult
  deriving Repr, DecidableEq

/--
  Exact `RRANGLES` hardware pipeline given the half-unit target vector's X-Z components
  `(ux, uz)` (for overflow / Y-axis singularity detection), Mode 1 angles `(t1, s1)` in
  15-bit 1's-complement revolutions (B-0), `RADMODES`, and scratch `(A, L)`.
  Computes:
  - `T(2) = 0.5 - T(1)` (`BDSU LODPHALF`)
  - `S(2) = S(1) + 0.5` (`DAD LODPHALF`)
  - `MODEB := 2V1STO2S(T2, S2)`, `MODEA := 2V1STO2S(T1, S1)`
  - Swaps `MODEA` and `MODEB` iff `ANTENBIT` is set in `RADMODES`.
-/
def rranglePipeline (ux uz : Int) (t1 s1 radmodes : Word15)
    (al : Word15 × Word15 := (POS_ZERO, POS_ZERO)) : RRAnglesResult :=
  if ux == 0 && uz == 0 then
    RRAnglesResult.gimbalLock
  else
    let t2 : Word15 := add15 HALF_REV (comp15 t1)   -- 0.5 - T(1)
    let s2 : Word15 := add15 s1 HALF_REV            -- S(1) + 0.5
    let mode1CDU := twoV1sTo2s (t1, s1)
    let mode2CDU := twoV1sTo2s (t2, s2)
    let (modeA, modeB) := rrangleModeSwap radmodes al mode1CDU mode2CDU
    RRAnglesResult.angles modeA modeB

-- ============================================================================
-- 5. `RRNB` & `RRNBMPAC` — EXACT FORWARD KINEMATICS & MODE 1/2 DUALITY (PAGE 324)
-- ============================================================================

/--
  Exact algebraic Mode 2 Trunnion angle `T(2) = 180° - T(1)`:
  `cos(π - T) = -cos(T)`, `sin(π - T) = sin(T)`.
-/
def mode2Trunnion {R : Type} [ExactCommRing R] (t : TrigAngle R) : TrigAngle R where
  c := ExactCommRing.neg t.c
  s := t.s
  unit := by
    rw [ExactCommRing.neg_mul_neg]
    exact t.unit

/--
  Exact algebraic Mode 2 Shaft angle `S(2) = 180° + S(1)`:
  `cos(S + π) = -cos(S)`, `sin(S + π) = -sin(S)`.
-/
def mode2Shaft {R : Type} [ExactCommRing R] (s : TrigAngle R) : TrigAngle R where
  c := ExactCommRing.neg s.c
  s := ExactCommRing.neg s.s
  unit := by
    rw [ExactCommRing.neg_mul_neg, ExactCommRing.neg_mul_neg]
    exact s.unit

/--
  `RRNB` / `RRNBMPAC` exact unit Line-of-Sight vector in Navigation Base axes
  (`LEM_GEOMETRY.agc`, Page 324, lines 158–159):
  `u(T, S) = (sin(S)cos(T), -sin(T), cos(S)cos(T))`.
  (In AGC memory, stored half-scaled as `0.5 * u(T, S)` in `32D, 34D, 36D` and `MPAC`.)
-/
def rrnbUnitLOS {R : Type} [ExactCommRing R] (t s : TrigAngle R) : Vec3 R :=
  ⟨ExactCommRing.mul s.s t.c, ExactCommRing.neg t.s, ExactCommRing.mul s.c t.c⟩

/--
  `RRNB` entry state modeling both entry points on Page 324:
  - `RRNB` reads `(T, S)` from `(TANGNB, TANGNB+1)` via `CDULOGIC`.
  - `RRNBMPAC` reads `(T, S)` from `(MPAC, MPAC+1)` via `CDULOGIC` (saving `MPAC+1` to `21D`).
-/
structure RRNBState where
  tangnb0 : Word15  -- `TANGNB` (Trunnion CDU)
  tangnb1 : Word15  -- `TANGNB + 1` (Shaft CDU)
  mpac0   : Word15  -- `MPAC` (Trunnion CDU for `RRNBMPAC`)
  mpac1   : Word15  -- `MPAC + 1` (Shaft CDU for `RRNBMPAC`)
  loc21   : Word15  -- `21D` temporary save location
  deriving Repr, DecidableEq

/-- `RRNB` (lines 166–187): decodes `(TANGNB, TANGNB+1)` via `CDULOGIC` and evaluates `losFn`. -/
def rrnbExec {α : Type} (losFn : Word15 → Word15 → Vec3 α) (st : RRNBState) : Vec3 α :=
  let tOnes := cduLogicToOnes15 st.tangnb0
  let sOnes := cduLogicToOnes15 st.tangnb1
  losFn tOnes sOnes

/-- `RRNBMPAC` (lines 191–205): saves `MPAC+1` to `21D`, decodes `(MPAC, 21D)` via `CDULOGIC`, jumps to `RRNB1`. -/
def rrnbMpacExec {α : Type} (losFn : Word15 → Word15 → Vec3 α) (st : RRNBState) : RRNBState × Vec3 α :=
  let st1 := { st with loc21 := st.mpac1 }
  let tOnes := cduLogicToOnes15 st1.mpac0
  let sOnes := cduLogicToOnes15 st1.loc21
  (st1, losFn tOnes sOnes)

-- ============================================================================
-- 6. KERNEL-VERIFIED THEOREMS (ZERO `sorry`, ZERO CUSTOM AXIOMS)
-- ============================================================================

-- 6.1 `SVDWN2` & `SVDWN1` State Vector Theorems
-- ----------------------------------------------------------------------------

/-- Universal theorem: When `AVEMIDSW` is clear, `SVDWN2` exits immediately (`RVQ`) without
    modifying any state vector register. -/
theorem svdwn2_noop_when_avemidsw_false (st : DownlinkState) (h : st.avemidsw = false) :
    svdwn2 st = st := by
  simp [svdwn2, h]

/-- Universal theorem: `SVDWN2` never clobbers `R-OTHER` or `V-OTHER`. -/
theorem svdwn2_preserves_other_state (st : DownlinkState) :
    (svdwn2 st).rOther = st.rOther ∧ (svdwn2 st).vOther = st.vOther := by
  unfold svdwn2
  cases st.avemidsw <;> simp

/-- Universal theorem: `SVDWN1` never clobbers `RN`, `VN`, or `PIPTIME`. -/
theorem svdwn1_preserves_own_state (st : DownlinkState) :
    (svdwn1 st).rn = st.rn ∧ (svdwn1 st).vn = st.vn ∧ (svdwn1 st).piptime = st.piptime := by
  simp [svdwn1]

/-- Universal theorem: When `AVEMIDSW = true`, `SVDWN2` writes the exact same `(R, V)`
    into `(RN, VN)` that `SVDWN1` writes into `(R-OTHER, V-OTHER)`, and latches `PIPTIME := TET`. -/
theorem svdwn1_svdwn2_same_kinematics (st : DownlinkState) (h : st.avemidsw = true) :
    (svdwn2 st).rn = (svdwn1 st).rOther ∧
    (svdwn2 st).vn = (svdwn1 st).vOther ∧
    (svdwn2 st).piptime = st.tet := by
  simp [svdwn2, svdwn1, h]

/-- Exact Earth-scaling theorem (`X2 = 0`, B-29 / B-7): zero deviation preserves `RCV` and `VCV` identically. -/
theorem svdwn2_earth_zero_deviation (st : DownlinkState)
    (hsw : st.avemidsw = true) (hx2 : st.x2 = 0)
    (hd : st.tdeltav = ⟨0, 0, 0⟩) (hn : st.tnuv = ⟨0, 0, 0⟩) :
    (svdwn2 st).rn = st.rcv ∧ (svdwn2 st).vn = st.vcv := by
  simp [svdwn2, computeDownlinkRV, agcShiftVec, agcShiftInt, vec3AddInt, hsw, hx2, hd, hn]

/-- Exact Lunar-to-B29 scaling theorem (`X2 = +2`, B-27 -> B-29, B-5 -> B-7):
    With zero deviation, `SVDWN2` divides `RCV` (B-27) and `VCV` (B-5) by exact factor `4 = 2^2`. -/
theorem svdwn2_lunar_b27_to_b29_exact (st : DownlinkState)
    (hsw : st.avemidsw = true) (hx2 : st.x2 = 2)
    (hd : st.tdeltav = ⟨0, 0, 0⟩) (hn : st.tnuv = ⟨0, 0, 0⟩) :
    (svdwn2 st).rn = ⟨Int.tdiv st.rcv.x 4, Int.tdiv st.rcv.y 4, Int.tdiv st.rcv.z 4⟩ ∧
    (svdwn2 st).vn = ⟨Int.tdiv st.vcv.x 4, Int.tdiv st.vcv.y 4, Int.tdiv st.vcv.z 4⟩ := by
  simp [svdwn2, computeDownlinkRV, agcShiftVec, agcShiftInt, vec3AddInt, hsw, hx2, hd, hn]

/-- Sign symmetry of AGC fixed-point shift (`agcShiftInt (-v) k = -agcShiftInt v k`). -/
theorem agcShiftInt_neg (v k : Int) :
    agcShiftInt (-v) k = -agcShiftInt v k := by
  unfold agcShiftInt
  split
  · rw [Int.neg_mul]
  · exact Int.neg_tdiv v _

-- 6.2 1's-Complement ↔ 2's-Complement CDU Conversion Theorems (`2V1STO2S` / `CDULOGIC`)
-- ----------------------------------------------------------------------------

/-- `2V1STO2S` maps both `+0` (`0o00000`) and `-0` (`0o77777`) to 2's-complement zero `0o00000`. -/
theorem onesToTwos15_zeros :
    onesToTwos15 POS_ZERO = POS_ZERO ∧ onesToTwos15 NEG_ZERO = POS_ZERO := by
  decide

/-- Helper: bit 14 (`0o40000#15`) of a 15-bit word is zero iff `w.toNat < 16384`. -/
private theorem bit14_clear_iff (w : Word15) :
    (w &&& 0o40000#15 = 0#15) ↔ w.toNat < 16384 := by
  have hlt : w.toNat < 32768 := w.isLt
  have h14 : w.getLsbD 14 = decide (16384 ≤ w.toNat) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
    by_cases h : 16384 ≤ w.toNat
    · have hdiv : w.toNat / 2 ^ 14 = 1 := by omega
      simp [h, hdiv]
    · have hdiv : w.toNat / 2 ^ 14 = 0 := by omega
      simp [h, hdiv]
  constructor
  · intro hz
    have hbit := congrArg (fun v => BitVec.getLsbD v 14) hz
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hbit
    have hm : (0o40000#15 : Word15).getLsbD 14 = true := by decide
    rw [hm, Bool.and_true, h14] at hbit
    by_cases h : 16384 ≤ w.toNat
    · simp [h] at hbit
    · omega
  · intro hlt14
    apply BitVec.eq_of_getLsbD_eq
    intro ⟨i, hi⟩
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    by_cases hi14 : i = 14
    · subst hi14
      rw [h14]
      have : ¬(16384 ≤ w.toNat) := by omega
      simp [this]
    · have hm : (0o40000#15 : Word15).getLsbD i = false := by
        have hpow : (0o40000#15 : Word15) = BitVec.ofNat 15 (2 ^ 14) := rfl
        rw [hpow, BitVec.getLsbD, BitVec.toNat_ofNat]
        have htb : Nat.testBit (2 ^ 14) i = false := by
          rw [Nat.testBit_two_pow]
          simp [Ne.symm hi14]
        simpa [Nat.testBit] using htb
      simp [hm]

/-- Universal roundtrip theorem: For every 15-bit ones'-complement word `w ≠ -0` (`0o77777`),
    `CDULOGIC (1STO2S w) = w` identically. -/
theorem cdu_roundtrip_exact (w : Word15) (hne : w ≠ NEG_ZERO) :
    cduLogicToOnes15 (onesToTwos15 w) = w := by
  unfold onesToTwos15 cduLogicToOnes15
  have hlt : w.toNat < 32768 := w.isLt
  have hne_nat : w.toNat ≠ 32767 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    simpa [NEG_ZERO] using h
  by_cases hsign : (w &&& 0o40000#15) = 0#15
  · simp [hsign]
  · have hbeq_f : (w &&& 0o40000#15 == 0#15) = false := beq_false_of_ne hsign
    simp only [hbeq_f, Bool.false_eq_true, ↓reduceIte]
    have hw_ge : 16384 ≤ w.toNat := by
      by_cases hlt14 : w.toNat < 16384
      · exact absurd ((bit14_clear_iff w).2 hlt14) hsign
      · omega
    have hadd_nat : (w + 1#15).toNat = w.toNat + 1 := by
      rw [BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      omega
    have hsign' : ((w + 1#15) &&& 0o40000#15) ≠ 0#15 := by
      intro hz
      have := (bit14_clear_iff (w + 1#15)).1 hz
      omega
    have hbeq'_f : ((w + 1#15) &&& 0o40000#15 == 0#15) = false := beq_false_of_ne hsign'
    have hnotmin : (w + 1#15 == 0o40000#15) = false := by
      apply beq_false_of_ne
      intro heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      omega
    simp only [hbeq'_f, hnotmin, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega

-- 6.3 `RRANGLES` Hardware Swap & Singularity Theorems
-- ----------------------------------------------------------------------------

/-- Universal theorem: The 3-instruction `DXCH MODEA; DXCH MODEB; DXCH MODEA` sequence
    losslessly swaps `MODEA` and `MODEB` and preserves the `(A, L)` register pair. -/
theorem dxch_three_step_swap_exact (al modeA modeB : Word15 × Word15) :
    dxchSwap al modeA modeB = (al, modeB, modeA) := by
  rfl

/-- Helper: masking any 15-bit word against single-bit `ANTENBIT` (`0o04000#15`, bit 11). -/
private theorem mask_antenbit_cases (w : Word15) :
    ((w &&& ANTENBIT = 0#15) ∧ (comp15 w &&& ANTENBIT = ANTENBIT)) ∨
    ((w &&& ANTENBIT = ANTENBIT) ∧ (comp15 w &&& ANTENBIT = 0#15)) := by
  have hm_other : ∀ i : Nat, i ≠ 11 → (ANTENBIT.getLsbD i = false) := by
    intro i hi
    have : ANTENBIT = BitVec.ofNat 15 (2 ^ 11) := rfl
    rw [this, BitVec.getLsbD, BitVec.toNat_ofNat]
    have htb : Nat.testBit (2 ^ 11) i = false := by
      rw [Nat.testBit_two_pow]
      simp [Ne.symm hi]
    simpa [Nat.testBit] using htb
  have hm_11 : ANTENBIT.getLsbD 11 = true := by decide
  cases hb : w.getLsbD 11
  · left
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro ⟨i, hi⟩
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
      by_cases h11 : i = 11
      · subst h11; simp [hb]
      · simp [hm_other i h11]
    · apply BitVec.eq_of_getLsbD_eq
      intro ⟨i, hi⟩
      simp only [comp15, BitVec.getLsbD_and, BitVec.getLsbD_not]
      by_cases h11 : i = 11
      · subst h11; simp [hb, hm_11]
      · simp [hm_other i h11]
  · right
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro ⟨i, hi⟩
      simp only [BitVec.getLsbD_and]
      by_cases h11 : i = 11
      · subst h11; simp [hb, hm_11]
      · simp [hm_other i h11]
    · apply BitVec.eq_of_getLsbD_eq
      intro ⟨i, hi⟩
      simp only [comp15, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
      by_cases h11 : i = 11
      · subst h11; simp [hb]
      · simp [hm_other i h11]

/-- Universal theorem: `RRANGLES` leaves `(MODEA, MODEB) = (Mode 1, Mode 2)` iff `ANTENBIT`
    is clear in `RADMODES`, and swaps them to `(Mode 2, Mode 1)` iff `ANTENBIT` is set. -/
theorem rrangleModeSwap_spec (radmodes : Word15) (al m1 m2 : Word15 × Word15) :
    rrangleModeSwap radmodes al m1 m2 =
      if (radmodes &&& ANTENBIT) == 0#15 then (m1, m2) else (m2, m1) := by
  unfold rrangleModeSwap
  rcases mask_antenbit_cases radmodes with ⟨hrm, ha⟩ | ⟨hrm, ha⟩
  · rw [hrm, ha]
    rfl
  · rw [hrm, ha]
    rfl

/-- Universal theorem: A target vector along the Navigation Base Y-axis (`ux = 0 ∧ uz = 0`)
    always triggers the `BOVB LUNDESCH` gimbal-lock maneuver branch. -/
theorem rrangles_y_axis_gimbal_lock (t1 s1 radmodes : Word15) (al : Word15 × Word15) :
    rranglePipeline 0 0 t1 s1 radmodes al = RRAnglesResult.gimbalLock := by
  rfl

-- 6.4 `RRNB` / `RRNBMPAC` Exact Algebraic Geometry & Mode 1/2 Duality Theorems
-- ----------------------------------------------------------------------------

/-- Universal theorem: `RRNB` and `RRNBMPAC` compute the exact same Line-of-Sight vector
    whenever `MPAC, MPAC+1` hold the same `(T, S)` CDU angles as `TANGNB, TANGNB+1`. -/
theorem rrnb_eq_rrnbmpac {α : Type} (losFn : Word15 → Word15 → Vec3 α) (st : RRNBState)
    (h0 : st.mpac0 = st.tangnb0) (h1 : st.mpac1 = st.tangnb1) :
    (rrnbMpacExec losFn st).2 = rrnbExec losFn st := by
  simp [rrnbMpacExec, rrnbExec, h0, h1]

/--
  Universal exact geometric theorem (`LEM_GEOMETRY.agc`, Page 322 & Page 324):
  Mode 1 angles `(T₁, S₁)` and Mode 2 angles `(T₂, S₂) = (180° - T₁, S₁ + 180°)`
  produce the **EXACT SAME** Line-of-Sight vector in Navigation Base axes, over ANY
  commutative ring `R` with zero approximations.
-/
theorem rrnb_mode1_eq_mode2 {R : Type} [ExactCommRing R] (t s : TrigAngle R) :
    rrnbUnitLOS (mode2Trunnion t) (mode2Shaft s) = rrnbUnitLOS t s := by
  unfold rrnbUnitLOS mode2Trunnion mode2Shaft
  simp only [ExactCommRing.neg_mul_neg]

/--
  Universal exact unit-norm theorem (`LEM_GEOMETRY.agc`, Page 324):
  For ALL Trunnion and Shaft angles `(T, S)` over ANY commutative ring `R`,
  `‖(sin(S)cos(T), -sin(T), cos(S)cos(T))‖² = 1` identically.
  (Hence the AGC half-unit output `0.5 * u` has exact squared norm `1/4`.)
-/
theorem rrnb_unit_norm_sq {R : Type} [ExactCommRing R] (t s : TrigAngle R) :
    vec3NormSq (rrnbUnitLOS t s) = ExactCommRing.one := by
  unfold vec3NormSq vec3Dot rrnbUnitLOS
  -- Terms: (s.s * t.c)*(s.s * t.c) + (-t.s)*(-t.s) + (s.c * t.c)*(s.c * t.c)
  have h1 : ExactCommRing.mul (ExactCommRing.mul s.s t.c) (ExactCommRing.mul s.s t.c) =
      ExactCommRing.mul (ExactCommRing.mul s.s s.s) (ExactCommRing.mul t.c t.c) := by
    rw [ExactCommRing.mul_assoc, ← ExactCommRing.mul_assoc t.c s.s t.c,
        ExactCommRing.mul_comm t.c s.s, ExactCommRing.mul_assoc s.s t.c t.c,
        ← ExactCommRing.mul_assoc]
  have h2 : ExactCommRing.mul (ExactCommRing.neg t.s) (ExactCommRing.neg t.s) =
      ExactCommRing.mul t.s t.s := ExactCommRing.neg_mul_neg t.s t.s
  have h3 : ExactCommRing.mul (ExactCommRing.mul s.c t.c) (ExactCommRing.mul s.c t.c) =
      ExactCommRing.mul (ExactCommRing.mul s.c s.c) (ExactCommRing.mul t.c t.c) := by
    rw [ExactCommRing.mul_assoc, ← ExactCommRing.mul_assoc t.c s.c t.c,
        ExactCommRing.mul_comm t.c s.c, ExactCommRing.mul_assoc s.c t.c t.c,
        ← ExactCommRing.mul_assoc]
  rw [h1, h2, h3]
  -- Group (s.s^2 * t.c^2 + s.c^2 * t.c^2) + t.s^2
  rw [ExactCommRing.add_comm (ExactCommRing.mul (ExactCommRing.mul s.s s.s) (ExactCommRing.mul t.c t.c)),
      ExactCommRing.add_assoc,
      ExactCommRing.add_comm (ExactCommRing.mul (ExactCommRing.mul s.s s.s) (ExactCommRing.mul t.c t.c)),
      ← ExactCommRing.right_distrib,
      s.unit, ExactCommRing.one_mul, ExactCommRing.add_comm, t.unit]

/--
  Universal exact `RRANGLES` ↔ `RRNB` recovery identity:
  For any unit LOS `u = rrnbUnitLOS t s`, negating the Y-component recovers `sin(T)`
  exactly (`-u.y = sin(T)`), and the X-Z projection `(u.x, 0, u.z)` satisfies
  `u.x² + u.z² = cos²(T)` identically.
-/
theorem rrangles_recovers_sinT_and_xz_proj {R : Type} [ExactCommRing R] (t s : TrigAngle R) :
    let u := rrnbUnitLOS t s
    ExactCommRing.neg u.y = t.s ∧
    ExactCommRing.add (ExactCommRing.mul u.x u.x) (ExactCommRing.mul u.z u.z) =
      ExactCommRing.mul t.c t.c := by
  dsimp only [rrnbUnitLOS]
  constructor
  · exact ExactCommRing.neg_neg t.s
  · have h1 : ExactCommRing.mul (ExactCommRing.mul s.s t.c) (ExactCommRing.mul s.s t.c) =
        ExactCommRing.mul (ExactCommRing.mul s.s s.s) (ExactCommRing.mul t.c t.c) := by
      rw [ExactCommRing.mul_assoc, ← ExactCommRing.mul_assoc t.c s.s t.c,
          ExactCommRing.mul_comm t.c s.s, ExactCommRing.mul_assoc s.s t.c t.c,
          ← ExactCommRing.mul_assoc]
    have h3 : ExactCommRing.mul (ExactCommRing.mul s.c t.c) (ExactCommRing.mul s.c t.c) =
        ExactCommRing.mul (ExactCommRing.mul s.c s.c) (ExactCommRing.mul t.c t.c) := by
      rw [ExactCommRing.mul_assoc, ← ExactCommRing.mul_assoc t.c s.c t.c,
          ExactCommRing.mul_comm t.c s.c, ExactCommRing.mul_assoc s.c t.c t.c,
          ← ExactCommRing.mul_assoc]
    rw [h1, h3, ExactCommRing.add_comm, ← ExactCommRing.right_distrib, s.unit, ExactCommRing.one_mul]

-- 6.5 Concrete Executable Hardware Verification Suite (`decide`)
-- ----------------------------------------------------------------------------

/-- Concrete verification of `SVDWN2` lunar scaling (`X2 = +2`, B-27 -> B-29, B-5 -> B-7). -/
def testLunarDownlinkState : DownlinkState :=
  { avemidsw := true
    x2       := 2
    tdeltav  := ⟨512, -1024, 2048⟩  -- B-18: shifted right 9 => (1, -2, 4) at B-27
    rcv      := ⟨3999, 8002, -12004⟩ -- B-27: + (1,-2,4) = (4000, 8000, -12000) >> 2 = (1000, 2000, -3000)
    tnuv     := ⟨64, -128, 192⟩     -- B-1: shifted right 6 => (1, -2, 3) at B-5
    vcv      := ⟨399, 802, -1203⟩   -- B-5: + (1,-2,3) = (400, 800, -1200) >> 2 = (100, 200, -300)
    tet      := 123456
    rn       := ⟨0, 0, 0⟩
    vn       := ⟨0, 0, 0⟩
    piptime  := 0
    rOther   := ⟨0, 0, 0⟩
    vOther   := ⟨0, 0, 0⟩ }

theorem verify_svdwn2_lunar_concrete :
    (svdwn2 testLunarDownlinkState).rn = ⟨1000, 2000, -3000⟩ ∧
    (svdwn2 testLunarDownlinkState).vn = ⟨100, 200, -300⟩ ∧
    (svdwn2 testLunarDownlinkState).piptime = 123456 := by
  decide

/-- Concrete verification of `RRANGLES` Mode 1 vs Mode 2 `ANTENBIT` swap. -/
theorem verify_rrangles_mode1_and_mode2 :
    rranglePipeline 100 200 0o01000#15 0o02000#15 0o00000#15 =
      RRAnglesResult.angles (0o01000#15, 0o02000#15) (0o17000#15, 0o22000#15) ∧
    rranglePipeline 100 200 0o01000#15 0o02000#15 ANTENBIT =
      RRAnglesResult.angles (0o17000#15, 0o22000#15) (0o01000#15, 0o02000#15) := by
  decide

end ApolloMission.LEMGeometry
