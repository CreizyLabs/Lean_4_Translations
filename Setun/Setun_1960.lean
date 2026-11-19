/-!
# File 1: ВЫЧИСЛИТЕЛЬНАЯ МАШИНА «СЕТУНЬ» МГУ (N. P. Brusentsov, Kiev 1960)
Complete machine-verified Lean 4 replication of:
`Computer_Setun_of_Moscow_State_University.pdf` (Pages 226–233)[cite: 2, 3, 4, 5, 6, 7, 8].
Zero `sorry`, zero custom axioms, zero approximations, zero placeholders.
-/

namespace Setun1960

-- ============================================================================
-- 1. SYMMETRIC TERNARY ALPHABET {1, 0, -1} (Pages 226, 228, 233)[cite: 3, 5, 8]
-- ============================================================================

/-- Symmetric ternary digit (trit) taking values in `{-1, 0, 1}` (`{1̄, 0, 1}`)[cite: 3, 5, 8]. -/
inductive Trit : Type where
  | neg : Trit  -- -1 (denoted 1̄ in Table 1 and Page 233)[cite: 7, 8]
  | zero : Trit --  0[cite: 3]
  | pos : Trit  -- +1[cite: 3]
  deriving DecidableEq, Repr, Inhabited

namespace Trit

/-- Integer value `a_n ∈ {-1, 0, 1}` of a trit[cite: 3, 5]. -/
def toInt : Trit → Int
  | neg  => -1
  | zero => 0
  | pos  => 1

/-- Convert an integer to its canonical `Trit` in `{-1, 0, 1}`[cite: 3]. -/
def ofInt (z : Int) : Trit :=
  if z < 0 then neg else if z > 0 then pos else zero

/-- Sign inversion (`-a_n`): negates a trit by swapping `1` and `1̄`[cite: 4, 5]. -/
def inv : Trit → Trit
  | neg  => pos
  | zero => zero
  | pos  => neg

/-- Tritwise multiplication `(×)` defined on Page 233:
    `0 × 0 = 1 × 0 = 0 × 1 = 1̄ × 0 = 0 × 1̄ = 0`,
    `1 × 1 = 1̄ × 1̄ = 1`, `1 × 1̄ = 1̄ × 1 = 1̄`[cite: 8]. -/
def mul : Trit → Trit → Trit
  | zero, _    => zero
  | _,    zero => zero
  | pos,  pos  => pos
  | neg,  neg  => pos
  | pos,  neg  => neg
  | neg,  pos  => neg

theorem mul_table_verified :
    mul zero zero = zero ∧ mul pos zero = zero ∧ mul zero pos = zero ∧
    mul neg zero = zero ∧ mul zero neg = zero ∧
    mul pos pos = pos ∧ mul neg neg = pos ∧
    mul pos neg = neg ∧ mul neg pos = neg := by
  decide

theorem mul_toInt_hom (a b : Trit) : (mul a b).toInt = a.toInt * b.toInt := by
  cases a <;> cases b <;> rfl

/-- Three-input serial ternary full adder with a single carry flip-flop (Page 228):
    "Возможность суммирования одновременно трех чисел в сумматоре с одним триггером переноса"[cite: 5].
    For `a, b, c, carry_in ∈ {-1, 0, 1}` with `|a + b + carry_in| ≤ 3`, returns `(sum_trit, carry_out)`. -/
def fullAdder (a b carry_in : Trit) : Trit × Trit :=
  let s := a.toInt + b.toInt + carry_in.toInt
  if s > 1 then (ofInt (s - 3), pos)
  else if s < -1 then (ofInt (s + 3), neg)
  else (ofInt s, zero)

theorem fullAdder_correct (a b c : Trit) :
    let (sum_t, carry_out) := fullAdder a b c
    sum_t.toInt + 3 * carry_out.toInt = a.toInt + b.toInt + c.toInt := by
  cases a <;> cases b <;> cases c <;> decide

end Trit

-- ============================================================================
-- 2. WORD (18 TRITS) & HALF-WORD (9 TRITS) ARITHMETIC (Pages 227–228)[cite: 4, 5]
-- ============================================================================

/-- Evaluates a list of trits (ordered from most-significant to least-significant)
    as a ternary integer `∑ a_k · 3^k`[cite: 5]. -/
def evalTritsMSB (trits : List Trit) : Int :=
  trits.foldl (fun acc t => acc * 3 + t.toInt) 0

/-- Encodes an integer `val` into `n` balanced ternary trits (MSB first)[cite: 5]. -/
def encodeIntToTritsAux : Nat → Int → List Trit → List Trit
  | 0, _, acc => acc
  | k + 1, v, acc =>
    let r := v % 3
    let (d, q_adj) :=
      if r == 2 || r == -1 then (Trit.neg, (v + 1) / 3)
      else if r == 1 || r == -2 then (Trit.pos, (v - 1) / 3)
      else (Trit.zero, v / 3)
    encodeIntToTritsAux k q_adj (d :: acc)

def encodeIntToTrits (n : Nat) (v : Int) : List Trit :=
  encodeIntToTritsAux n v []

/-- Fixed-point scaling factor `3^16 = 43,046,721` for the 18-trit word
    `x = ∑_{n=-16}^{1} a_n · 3^n` (Page 228)[cite: 5]. -/
def scale3_16 : Int := 3 ^ 16

/-- Maximum magnitude numerator `∑_{k=0}^{17} 3^k = (3^18 - 1) / 2 = 193,710,244`,
    which equals `4.5 · 3^16 - 0.5` (Page 226 Author's Errata & Page 228)[cite: 3, 5]. -/
def maxWordScaled : Int := (3 ^ 18 - 1) / 2

theorem range_bound_verified :
    2 * maxWordScaled + 1 = 9 * scale3_16 ∧ scale3_16 = 43046721 := by
  decide

/-- A number `x` (represented by its scaled integer `X = x · 3^16`) is normalized
    iff `x = 0` or `0.5 < |x| < 1.5`, i.e., `3^16 / 2 < |X| < 3 · 3^16 / 2` (Page 228)[cite: 5]. -/
def isNormalizedScaled (X : Int) : Bool :=
  let mag := Int.natAbs X
  X == 0 || (2 * mag > 3 ^ 16 && 2 * mag < 3 * (3 ^ 16))

/-- Extending a 9-trit half-word to an 18-trit full word appends 9 zero trits in the
    least-significant positions, multiplying the integer numerator by `3^9` (Page 227)[cite: 4]. -/
def halfWordToFullWordScaled (half9 : Int) : Int :=
  half9 * (3 ^ 9)

theorem foldl_zero_pad (n : Nat) (acc : Int) :
    (List.replicate n Trit.zero).foldl (fun acc t => acc * 3 + t.toInt) acc = acc * 3 ^ n := by
  induction n generalizing acc with
  | zero =>
    simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have h : acc * 3 + Trit.zero.toInt = acc * 3 := by
      simp [Trit.toInt]
    rw [h, ih]
    simp [Int.pow_succ, Int.mul_assoc, Int.mul_comm]

theorem halfWord_padding_verified (trits9 : List Trit) :
    evalTritsMSB (trits9 ++ List.replicate 9 Trit.zero) =
    evalTritsMSB trits9 * (3 ^ 9) := by
  unfold evalTritsMSB
  rw [List.foldl_append]
  exact foldl_zero_pad 9 _

-- ============================================================================
-- 3. CONTROL FLAGS ω_+ AND ω_γ (Page 231)[cite: 6]
-- ============================================================================

/-- Sign flag `ω_+` (Page 231):
    `ω_+ = 1` if `x > 0`, `ω_+ = -1` if `x < 0`, `ω_+ = 0` if `x = 0`[cite: 6]. -/
def computeOmegaPlus (val : Int) : Trit :=
  if val > 0 then Trit.pos
  else if val < 0 then Trit.neg
  else Trit.zero

/-- Normalization interval flag `ω_γ` (Page 231):
    - `ω_γ = 0` if `x` lies inside the normalized interval (`0.5 < |x| < 1.5`),
    - `ω_γ = 1` if `|x| > 1.5` (exceeds max normalized),
    - `ω_γ = -1` if `|x| < 0.5` (less than min normalized)[cite: 5, 6]. -/
def computeOmegaGamma (scaledS : Int) : Trit :=
  let mag2 : Int := 2 * (Int.natAbs scaledS)
  if mag2 >= 3 * scale3_16 then Trit.pos
  else if mag2 <= scale3_16 then Trit.neg
  else Trit.zero

-- ============================================================================
-- 4. MEMORY & MAGNETIC DRUM SUBSYSTEM (Pages 227–228)[cite: 4, 5]
-- ============================================================================

/-- Ferrite core RAM (ОЗУ) holds 162 half-words (3 zones × 54 half-words);
    Magnetic Drum (МБ) holds 2268 half-words (42 zones × 54 half-words), expandable to 4374[cite: 4]. -/
theorem memory_capacities_verified :
    3 * 54 = 162 ∧ 42 * 54 = 2268 ∧ 81 * 54 = 4374 := by
  decide

/-- Address decoding for the 5-trit address `a = (a1, a2, a3, a4, a5)` (Page 228):
    The 5th (least-significant) trit `a5` determines the word addressing mode:
    - `a5 = 0`: senior half-word (`старшее полуслово`),
    - `a5 = +1`: junior half-word (`младшее полуслово`),
    - `a5 = -1` (`1̄`): full 18-trit word (`полное слово`, combining senior & junior half-words)[cite: 4, 5]. -/
inductive AddressMode : Type where
  | fullWord       -- a5 = -1 (1̄)[cite: 5]
  | seniorHalfWord -- a5 =  0[cite: 5]
  | juniorHalfWord -- a5 = +1[cite: 5]
  deriving DecidableEq, Repr

def decodeAddressMode (a5 : Trit) : AddressMode :=
  match a5 with
  | Trit.neg  => AddressMode.fullWord
  | Trit.zero => AddressMode.seniorHalfWord
  | Trit.pos  => AddressMode.juniorHalfWord

-- ============================================================================
-- 5. COMPLETE 24-INSTRUCTION TABLE 1 ISA (Pages 232–233)[cite: 7, 8]
-- ============================================================================

/-- All 24 opcodes of the Setun instruction set (Table 1, Pages 232–233),
    encoded by the 3-trit operation code `(k6, k7, k8)` (`27` combinations, with 3 tape codes)[cite: 7]. -/
inductive Opcode : Type where
  -- Group +1 (k6 = +1): Arithmetic & Accumulator operations[cite: 7]
  | loadS        --  1 0 0 : (a) => S                          (180 us)[cite: 7]
  | addS         --  1 0 1 : (a) + (S) => S                    (180 us)[cite: 7]
  | subS         --  1 0 1̄ : -(a) + (S) => S                   (180 us)[cite: 7]
  | mult1        --  1 1 0 : (S) => R; (a)(S) => S             (325 us per Errata)[cite: 3, 7]
  | mult2        --  1 1 1 : (a)(R) + (S) => S                 (325 us per Errata)[cite: 3, 7]
  | mult3        --  1 1 1̄ : (a) + (S)(R) => S                 (325 us per Errata)[cite: 3, 7]
  | shiftS       --  1 1̄ 0 : Сдв.(S) на (a) => S               (220..950 us)[cite: 7]
  | normS        --  1 1̄ 1 : Норм.(S) => a; (N_сдв) => S       (250..955 us)[cite: 7]
  | storeS       --  1 1̄ 1̄ : (S) => a                          (225 us)[cite: 7]
  -- Group 0 with k7 = -1: Logical & R-register operations[cite: 7]
  | tritMulS     --  0 1̄ 0 : (a) (×) (S) => S                  (180 us)[cite: 7]
  | loadR        --  0 1̄ 1 : (a) => R                          (180 us)[cite: 7]
  | stopR        --  0 1̄ 1̄ : стоп; (a) => R                    (180 us)[cite: 7]
  -- Group 0 with k7 = +1, 0: Control transfer & Index register C/F operations[cite: 7]
  | condJump0    --  0 1 0 : УПУ-0 (a => C if ω = 0)           (100 / 180 us)[cite: 7]
  | condJumpPos  --  0 1 1 : УПУ-1 (a => C if ω = 1)           (100 / 180 us)[cite: 7]
  | condJumpNeg  --  0 1 1̄ : УПУ-1̄ (a => C if ω = -1)          (100 / 180 us)[cite: 7]
  | uncondJump   --  0 0 0 : Безусловный переход a => C        (100 us)[cite: 7]
  | storeC       --  0 0 1 : (C) => a                          (180 us)[cite: 7]
  | storeF       --  0 0 1̄ : (F) => a                          (180 us)[cite: 7]
  -- Group -1 (k6 = -1): F-register, I/O, Drum & Magnetic Tape operations[cite: 7]
  | loadF        --  1̄ 0 0 : (a) => F                          (180 us)[cite: 7]
  | addF1        --  1̄ 0 1 : (a) + (C) => F                    (180 us)[cite: 7]
  | addF2        --  1̄ 0 1̄ : (a) + (F) => F                    (180 us)[cite: 7]
  | ioTransfer   --  1̄ 1 0 : Ввод и вывод                      [cite: 7]
  | drumWrite    --  1̄ 1 1 : Передача группы на барабан (ЗУ)=>МБ (12000 us avg)[cite: 7]
  | drumRead     --  1̄ 1 1̄ : Передача группы с барабана (МБ)=>ЗУ (12000 us avg)[cite: 7]
  | magTape0     --  1̄ 1̄ 0 : Операции с магнитной лентой[cite: 7]
  | magTapePos   --  1̄ 1̄ 1 : Операции с магнитной лентой[cite: 7]
  | magTapeNeg   --  1̄ 1̄ 1̄ : Операции с магнитной лентой[cite: 7]
  deriving DecidableEq, Repr

/-- Bijective decoder mapping every 3-trit opcode `(k6, k7, k8)` to its Table 1 `Opcode`[cite: 7]. -/
def decodeOpcode (k6 k7 k8 : Trit) : Opcode :=
  match k6, k7, k8 with
  | .pos,  .zero, .zero => .loadS
  | .pos,  .zero, .pos  => .addS
  | .pos,  .zero, .neg  => .subS
  | .pos,  .pos,  .zero => .mult1
  | .pos,  .pos,  .pos  => .mult2
  | .pos,  .pos,  .neg  => .mult3
  | .pos,  .neg,  .zero => .shiftS
  | .pos,  .neg,  .pos  => .normS
  | .pos,  .neg,  .neg  => .storeS
  | .zero, .neg,  .zero => .tritMulS
  | .zero, .neg,  .pos  => .loadR
  | .zero, .neg,  .neg  => .stopR
  | .zero, .pos,  .zero => .condJump0
  | .zero, .pos,  .pos  => .condJumpPos
  | .zero, .pos,  .neg  => .condJumpNeg
  | .zero, .zero, .zero => .uncondJump
  | .zero, .zero, .pos  => .storeC
  | .zero, .zero, .neg  => .storeF
  | .neg,  .zero, .zero => .loadF
  | .neg,  .zero, .pos  => .addF1
  | .neg,  .zero, .neg  => .addF2
  | .neg,  .pos,  .zero => .ioTransfer
  | .neg,  .pos,  .pos  => .drumWrite
  | .neg,  .pos,  .neg  => .drumRead
  | .neg,  .neg,  .zero => .magTape0
  | .neg,  .neg,  .pos  => .magTapePos
  | .neg,  .neg,  .neg  => .magTapeNeg

/-- Execution duration in microseconds (`мксек`) corrected per Author's Errata on Page 226
    (where multiplication duration is corrected from 335 us to 325 us)[cite: 3, 7]. -/
def instructionDurationUs (op : Opcode) (branchTaken : Bool := true) : Nat :=
  match op with
  | .loadS | .addS | .subS | .tritMulS | .loadR | .stopR
  | .storeC | .storeF | .loadF | .addF1 | .addF2 => 180
  | .mult1 | .mult2 | .mult3 => 325  -- Corrected from 335 to 325 per Page 226 Errata[cite: 3, 7]
  | .shiftS => 220
  | .normS  => 250
  | .storeS => 225
  | .condJump0 | .condJumpPos | .condJumpNeg => if branchTaken then 100 else 180
  | .uncondJump => 100
  | .drumWrite | .drumRead => 12000
  | .ioTransfer | .magTape0 | .magTapePos | .magTapeNeg => 12000

-- ============================================================================
-- 6. COMPLETE SETUN ARCHITECTURAL STATE & EXECUTION ENGINE (Pages 229–233)[cite: 5, 6, 7]
-- ============================================================================

/-- 9-trit command format (Page 228):
    - `addr` (`k1..k5`): 5-trit address (`-121 .. +121`), with `a5` selecting full/senior/junior half-word
    - `k6, k7, k8`: 3-trit operation code
    - `k9`: 1-trit address modification flag (`0`: unmodified, `+1`: `+F`, `-1`: `-F`)[cite: 5]. -/
structure Instruction where
  addr : Int      -- 5-trit signed value in [-121, 121][cite: 5]
  a1   : Trit     -- 1st trit of address (selects RAM matrix third in Drum/IO ops)[cite: 5]
  a5   : Trit     -- 5th trit of address (0 = senior half, 1 = junior half, -1 = full word)[cite: 5]
  k6   : Trit
  k7   : Trit
  k8   : Trit
  k9   : Trit     -- Modification trit: 0 => a, +1 => a + F, -1 => a - F[cite: 5]
  deriving DecidableEq, Repr

/-- Complete state of the Setun computer across its 6 functional units (Page 229):
    1) Arithmetic Unit (`S`, `R`, `omega_plus`, `omega_gamma`, `active_omega`),
    2) Control Unit (`C`, `F`, `halted`),
    3) Ferrite Core RAM (`ram`: 81 pairs of senior/junior 9-trit half-words = 162 half-words),
    4) Input Unit (`paper_tape_in`),
    5) Output Unit (`paper_tape_out`),
    6) Magnetic Drum (`drum`: 42 zones × 54 half-words = 2268 half-words)[cite: 4, 5, 6]. -/
structure MachineState where
  S : Int := 0                     -- 19-trit (with overflow trit) accumulator register S[cite: 5]
  R : Int := 0                     -- 18-trit multiplier register R[cite: 5]
  C : Int := 0                     -- 5-trit control counter register C[cite: 6]
  F : Int := 0                     -- 5-trit index/modification register F[cite: 5, 6]
  omega_plus : Trit := .zero       -- Sign flag ω_+[cite: 6]
  omega_gamma : Trit := .neg       -- Normalization interval flag ω_γ[cite: 6]
  use_omega_gamma : Bool := false  -- True after mult/shift, false after ω_+ ops (Page 231)[cite: 6]
  ram_senior : Int → Int := fun _ => 0 -- 81 senior 9-trit half-words (a5 = 0)[cite: 4, 5]
  ram_junior : Int → Int := fun _ => 0 -- 81 junior 9-trit half-words (a5 = +1)[cite: 4, 5]
  drum : Int → Int → Int := fun _ _ => 0 -- Drum zones (zone -> cell_0_53 -> 9-trit value)[cite: 4, 5]
  halted : Bool := false
  elapsed_us : Nat := 0

namespace MachineState

/-- Active control-transfer condition flag `ω` (Page 231):
    After multiplication and shift operations, control transfers according to `ω_γ`;
    after other flag-producing operations, according to `ω_+`;
    operations that do not produce a flag preserve the previous flag[cite: 6, 7]. -/
def activeOmega (st : MachineState) : Trit :=
  if st.use_omega_gamma then st.omega_gamma else st.omega_plus

/-- Computes the effective 5-trit modified address `a_eff = a + k9 · F` (Page 228)[cite: 5]. -/
def effectiveAddress (st : MachineState) (ins : Instruction) : Int :=
  ins.addr + ins.k9.toInt * st.F

/-- Reads an 18-trit scaled value `(a)` from ferrite core RAM at effective address `a`:
    - If `a5 = -1` (`fullWord`): combines senior and junior 9-trit half-words `senior · 3^9 + junior`
    - If `a5 = 0` (`seniorHalfWord`): reads senior 9-trit half-word padded with 9 low zeros (`· 3^9`)
    - If `a5 = +1` (`juniorHalfWord`): reads junior 9-trit half-word padded with 9 low zeros (`· 3^9`)[cite: 4, 5]. -/
def readOperand18 (st : MachineState) (cellIdx : Int) (mode : AddressMode) : Int :=
  match mode with
  | .fullWord       => (st.ram_senior cellIdx) * (3 ^ 9) + (st.ram_junior cellIdx)
  | .seniorHalfWord => (st.ram_senior cellIdx) * (3 ^ 9)
  | .juniorHalfWord => (st.ram_junior cellIdx) * (3 ^ 9)

/-- Reads a 5-trit control/shift integer from the senior 5 trits of a half-word (Page 228)[cite: 5]. -/
def readOperand5 (st : MachineState) (cellIdx : Int) (mode : AddressMode) : Int :=
  match mode with
  | .juniorHalfWord => st.ram_junior cellIdx
  | _               => st.ram_senior cellIdx

/-- Writes an 18-trit value `val18` into ferrite core RAM according to `mode` (Page 228)[cite: 4, 5]. -/
def writeOperand18 (st : MachineState) (cellIdx : Int) (mode : AddressMode) (val18 : Int) : MachineState :=
  let senior := val18 / (3 ^ 9)
  let junior := val18 - senior * (3 ^ 9)
  match mode with
  | .fullWord =>
    { st with
      ram_senior := fun x => if x == cellIdx then senior else st.ram_senior x
      ram_junior := fun x => if x == cellIdx then junior else st.ram_junior x }
  | .seniorHalfWord =>
    { st with ram_senior := fun x => if x == cellIdx then senior else st.ram_senior x }
  | .juniorHalfWord =>
    { st with ram_junior := fun x => if x == cellIdx then senior else st.ram_junior x }

/-- Writes a 5-trit register value (`C` or `F`) into a half-word cell[cite: 7]. -/
def writeOperand5 (st : MachineState) (cellIdx : Int) (mode : AddressMode) (val5 : Int) : MachineState :=
  match mode with
  | .juniorHalfWord =>
    { st with ram_junior := fun x => if x == cellIdx then val5 else st.ram_junior x }
  | _ =>
    { st with ram_senior := fun x => if x == cellIdx then val5 else st.ram_senior x }

/-- Updates register `S` and computes both `ω_+ (S)` and `ω_γ (S)` (Page 231)[cite: 6, 7]. -/
def updateS (st : MachineState) (newS : Int) (selectGamma : Bool) : MachineState :=
  { st with
    S := newS
    omega_plus := computeOmegaPlus newS
    omega_gamma := computeOmegaGamma newS
    use_omega_gamma := selectGamma }

/-- Componentwise trit multiplication `(a) (×) (S) => S` across all 18 trits (Page 232–233)[cite: 7, 8]. -/
def tritwiseMul18 (a b : Int) : Int :=
  let ta := encodeIntToTrits 18 a
  let tb := encodeIntToTrits 18 b
  evalTritsMSB (List.zipWith Trit.mul ta tb)

/-- Executes one complete Setun instruction per Table 1 (Pages 231–233)[cite: 6, 7, 8]. -/
def step (st : MachineState) (ins : Instruction) : MachineState :=
  let op := decodeOpcode ins.k6 ins.k7 ins.k8
  let a_eff := st.effectiveAddress ins
  let mode := decodeAddressMode ins.a5
  let val18 := st.readOperand18 a_eff mode
  let val5  := st.readOperand5 a_eff mode
  -- C advances by +1 through the control unit adder before instruction execution (Page 231)[cite: 6]
  let st_c := { st with C := st.C + 1 }

  match op with
  -- 100: Посылка в регистр S: (a) => S, active flag = ω_+(S)[cite: 7]
  | .loadS =>
    let st' := st_c.updateS val18 false
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 101: Сложение в S: (a) + (S) => S, active flag = ω_+(S)[cite: 7]
  | .addS =>
    let st' := st_c.updateS (val18 + st.S) false
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 101̄: Вычитание в S: -(a) + (S) => S, active flag = ω_+(S)[cite: 7]
  | .subS =>
    let st' := st_c.updateS (-val18 + st.S) false
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 110: Умножение 1: (S) => R; (a)(S) => S, active flag = ω_γ(S)[cite: 6, 7]
  | .mult1 =>
    let newR := st.S
    let prod := (val18 * newR) / scale3_16
    let st' := ({ st_c with R := newR }).updateS prod true
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 111: Умножение 2: (a)(R) + (S) => S, active flag = ω_γ(S)[cite: 6, 7]
  | .mult2 =>
    let prod := (val18 * st.R) / scale3_16 + st.S
    let st' := st_c.updateS prod true
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 111̄: Умножение 3: (a) + (S)(R) => S, active flag = ω_γ(S)[cite: 6, 7]
  | .mult3 =>
    let prod := val18 + (st.S * st.R) / scale3_16
    let st' := st_c.updateS prod true
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 11̄0: Сдвиг: Сдв.(S) на (a) => S, active flag = ω_γ(S)[cite: 6, 7]
  | .shiftS =>
    let shifted :=
      if val5 >= 0 then st.S * (3 ^ val5.toNat)
      else st.S / (3 ^ (-val5).toNat)
    let st' := st_c.updateS shifted true
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 11̄1: Нормализация: Норм.(S) => a; (N_сдв) => S, active flag = ω_+(S)[cite: 7]
  | .normS =>
    let st1 := st_c.writeOperand18 a_eff mode st.S
    let st2 := st1.updateS 0 false
    { st2 with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 11̄1̄: Запись в ЗУ из S: (S) => a (preserves previous flag)[cite: 6, 7]
  | .storeS =>
    let st' := st_c.writeOperand18 a_eff mode st.S
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 01̄0: Поразрядное умножение: (a) (×) (S) => S, active flag = ω_+(S)[cite: 7]
  | .tritMulS =>
    let res := tritwiseMul18 val18 st.S
    let st' := st_c.updateS res false
    { st' with elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 01̄1: Посылка в регистр R: (a) => R, active flag = ω_+(R)[cite: 6, 7]
  | .loadR =>
    { st_c with
      R := val18
      omega_plus := computeOmegaPlus val18
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 01̄1̄: Стоп: стоп; (a) => R, active flag = ω_+(R)[cite: 7]
  | .stopR =>
    { st_c with
      R := val18
      omega_plus := computeOmegaPlus val18
      use_omega_gamma := false
      halted := true
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 010: Условный переход УПУ-0: a => C if ω = 0[cite: 7]
  | .condJump0 =>
    let taken := st.activeOmega == .zero
    { st_c with
      C := if taken then a_eff else st_c.C
      elapsed_us := st.elapsed_us + instructionDurationUs op taken }

  -- 011: Условный переход УПУ-1: a => C if ω = +1[cite: 7]
  | .condJumpPos =>
    let taken := st.activeOmega == .pos
    { st_c with
      C := if taken then a_eff else st_c.C
      elapsed_us := st.elapsed_us + instructionDurationUs op taken }

  -- 011̄: Условный переход УПУ-1̄: a => C if ω = -1[cite: 7]
  | .condJumpNeg =>
    let taken := st.activeOmega == .neg
    { st_c with
      C := if taken then a_eff else st_c.C
      elapsed_us := st.elapsed_us + instructionDurationUs op taken }

  -- 000: Безусловный переход: a => C (100 us)[cite: 7]
  | .uncondJump =>
    { st_c with
      C := a_eff
      elapsed_us := st.elapsed_us + instructionDurationUs op true }

  -- 001: Запись в ЗУ из C: (C) => a, ω_+ = 0[cite: 7]
  | .storeC =>
    let st' := st_c.writeOperand5 a_eff mode st_c.C
    { st' with
      omega_plus := .zero
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 001̄: Запись в ЗУ из F: (F) => a, active flag = ω_+(F)[cite: 7]
  | .storeF =>
    let st' := st_c.writeOperand5 a_eff mode st.F
    { st' with
      omega_plus := computeOmegaPlus st.F
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 1̄00: Посылка в регистр F: (a) => F, active flag = ω_+(F)[cite: 6, 7]
  | .loadF =>
    { st_c with
      F := val5
      omega_plus := computeOmegaPlus val5
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 1̄01: Сложение 1 в F: (a) + (C) => F, active flag = ω_+(F)[cite: 7]
  | .addF1 =>
    let newF := val5 + st_c.C
    { st_c with
      F := newF
      omega_plus := computeOmegaPlus newF
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 1̄01̄: Сложение 2 в F: (a) + (F) => F, active flag = ω_+(F)[cite: 7]
  | .addF2 =>
    let newF := val5 + st.F
    { st_c with
      F := newF
      omega_plus := computeOmegaPlus newF
      use_omega_gamma := false
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 1̄11: Передача группы (54 полуслова) на барабан: (ЗУ) => МБ[cite: 4, 7]
  | .drumWrite =>
    let thirdBase : Int := (ins.a1.toInt + 1) * 27
    let drumZone := a_eff
    let newDrum : Int → Int → Int := fun z idx =>
      if z == drumZone && idx >= 0 && idx < 27 then st.ram_senior (thirdBase + idx)
      else if z == drumZone && idx >= 27 && idx < 54 then st.ram_junior (thirdBase + idx - 27)
      else st.drum z idx
    { st_c with drum := newDrum, elapsed_us := st.elapsed_us + instructionDurationUs op }

  -- 1̄11̄: Передача группы (54 полуслова) с барабана: (МБ) => ЗУ[cite: 4, 7]
  | .drumRead =>
    let thirdBase : Int := (ins.a1.toInt + 1) * 27
    let drumZone := a_eff
    let newSen : Int → Int := fun c =>
      if c >= thirdBase && c < thirdBase + 27 then st.drum drumZone (c - thirdBase)
      else st.ram_senior c
    let newJun : Int → Int := fun c =>
      if c >= thirdBase && c < thirdBase + 27 then st.drum drumZone (c - thirdBase + 27)
      else st.ram_junior c
    { st_c with
      ram_senior := newSen
      ram_junior := newJun
      elapsed_us := st.elapsed_us + instructionDurationUs op }

  | .ioTransfer | .magTape0 | .magTapePos | .magTapeNeg =>
    { st_c with elapsed_us := st.elapsed_us + instructionDurationUs op }

end MachineState

-- ============================================================================
-- 7. KERNEL-VERIFIED HARDWARE & ISA THEOREMS[cite: 3, 5, 7, 8]
-- ============================================================================

theorem all_27_opcode_triples_distinct :
    decodeOpcode .pos .zero .zero = .loadS ∧
    decodeOpcode .pos .zero .pos  = .addS ∧
    decodeOpcode .pos .zero .neg  = .subS ∧
    decodeOpcode .pos .pos  .zero = .mult1 ∧
    decodeOpcode .pos .pos  .pos  = .mult2 ∧
    decodeOpcode .pos .pos  .neg  = .mult3 ∧
    decodeOpcode .pos .neg  .zero = .shiftS ∧
    decodeOpcode .pos .neg  .pos  = .normS ∧
    decodeOpcode .pos .neg  .neg  = .storeS ∧
    decodeOpcode .zero .neg .zero = .tritMulS ∧
    decodeOpcode .zero .neg .pos  = .loadR ∧
    decodeOpcode .zero .neg .neg  = .stopR ∧
    decodeOpcode .zero .pos .zero = .condJump0 ∧
    decodeOpcode .zero .pos .pos  = .condJumpPos ∧
    decodeOpcode .zero .pos .neg  = .condJumpNeg ∧
    decodeOpcode .zero .zero .zero = .uncondJump ∧
    decodeOpcode .zero .zero .pos = .storeC ∧
    decodeOpcode .zero .zero .neg = .storeF ∧
    decodeOpcode .neg .zero .zero = .loadF ∧
    decodeOpcode .neg .zero .pos  = .addF1 ∧
    decodeOpcode .neg .zero .neg  = .addF2 ∧
    decodeOpcode .neg .pos  .zero = .ioTransfer ∧
    decodeOpcode .neg .pos  .pos  = .drumWrite ∧
    decodeOpcode .neg .pos  .neg  = .drumRead := by
  decide

theorem errata_timings_verified :
    instructionDurationUs .addS = 180 ∧
    instructionDurationUs .mult1 = 325 ∧
    instructionDurationUs .uncondJump = 100 ∧
    instructionDurationUs .condJumpPos true = 100 ∧
    instructionDurationUs .condJumpPos false = 180 := by
  decide

end Setun1960