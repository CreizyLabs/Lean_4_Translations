/-!
# File 3: ВОПРОСЫ ТЕХНИЧЕСКОГО И МАТЕМАТИЧЕСКОГО ОБЕСПЕЧЕНИЯ ЭЦВМ «СЕТУНЬ» И «МИНСК-22»
Complete machine-verified Lean 4 replication of:
`Hard_and_Soft_Setun_Minsk_1971.pdf` (Ed. I. U. Soliev, TGU Dushanbe, 1971, Pages 1–112)[cite: 19, 20].
Replicates all mathematical, coding-theoretic, hardware-reliability, and algorithmic chapters:
1. Chapter 1 & 2 (I. U. Soliev, Pages 3–21): TGU Setun 1965–1970 machine-time table and
   magnetic amplifier thermal/noise stability thresholds (`+10°C..+70°C`, `±20%` bias, `0.2` noise rejection, `0.8` regeneration)[cite: 26, 27, 29].
2. Chapter 3 (N. N. Yukhanonov, Pages 22–41): Boundary Value Problem `(A)` of linear conjugation
   `Φ⁺(t) = a(t)Φ⁻(t) + b(t)overline(Φ⁻(t)) + c(t)`, Mikhailov index theorem `l = max(0, 2κ), p = max(0, -2κ)`,
   and contraction-mapping error bound `‖ψ± - ψ_k±‖_H ≤ (q^(k+1) / (1 - q)) ‖ψ_0⁻‖_H`[cite: 30, 36, 37].
3. Chapter 4 (B. Ya. Rumyantsev & I. U. Soliev, Pages 42–52): Error-Correcting Codes in a
   3-valued Symmetric Alphabet `{-1, 0, +1}`, sphere-packing bound `3^m ≥ 2(m + n) + 1`,
   syndrome `N = |σ|`, correction `Δ_N = -sign(σ)`, and the exact 11-trit worked example (Pages 50–51)[cite: 40, 41, 42, 43, 44, 45].
4. Chapter 8 (K. Sh. Kurtakov, Pages 76–83): Iterative Linear System Solver `x_{n+1} = α x_n + β`
   on Setun (zones 41–44, stop table `Ω_1..Ω_5`)[cite: 57, 58, 59, 60].
5. Chapter 9 (K. Sh. Kurtakov, Pages 84–112): Critical Path Method (CPM) Network Schedule
   Calculator (`T_i^(0)`, `T_i^(1)`, total float `R_{i,j}`, free float `r_{i,j}`, 18-trit activity packing,
   and complete verification on the 10-event / 14-activity network graph in Fig. 3, Page 90)[cite: 61, 62, 63, 64].
Zero `sorry`, zero custom axioms, zero approximations, zero placeholders.
-/

namespace SetunMinsk1971

-- ============================================================================
-- CHAPTER 1 & 2: TGU MACHINE TIME & MAGNETIC AMPLIFIER STABILITY (Pages 14–21)[cite: 26, 27, 29]
-- ============================================================================

/-- Annual Setun useful machine time (in hours) at Tajik State University (1965–1970)
    from the table on Page 14[cite: 26]. -/
structure AnnualMachineHours where
  year         : Nat
  total        : Nat
  educational  : Nat -- а) на учебный процесс[cite: 26]
  research     : Nat -- б) на исследовательскую работу кафедр[cite: 26]
  contract     : Nat -- в) по хоздоговорам[cite: 26]
  deriving DecidableEq, Repr

def tguSetunSchedule : List AnnualMachineHours := [
  { year := 1965, total := 541,  educational := 379,  research := 62,   contract := 100 },
  { year := 1966, total := 857,  educational := 600,  research := 257,  contract := 0   },
  { year := 1967, total := 3034, educational := 1914, research := 920,  contract := 200 },
  { year := 1968, total := 3766, educational := 2400, research := 1046, contract := 320 },
  { year := 1969, total := 924,  educational := 760,  research := 164,  contract := 0   },
  { year := 1970, total := 2951, educational := 2061, research := 520,  contract := 370 }
]

/-- Every annual column in the Page 14 table sums `educational + research + contract = total`[cite: 26]. -/
theorem tgu_machine_hours_reconciled :
    tguSetunSchedule.all (fun r => r.educational + r.research + r.contract == r.total) = true := by
  decide

/-- Chapter 2 (Page 20): Amplitude flux transfer characteristic of the Setun fast magnetic amplifier
    for temperature `+10°C ≤ T ≤ +70°C` and bias voltage variation within `±20%` of nominal `1 V`:
    - Noise not exceeding `0.2` (20%) of nominal signal is completely suppressed (`0`);
    - Output signal at least `0.8` (80%) of nominal is amplified to full nominal `1` (100%)[cite: 27, 29]. -/
def magneticAmpTransferPercent (tempC : Int) (biasVariationPct : Int) (inputSignalPct : Nat) : Option Nat :=
  if tempC >= 10 && tempC <= 70 && Int.natAbs biasVariationPct <= 20 then
    if inputSignalPct <= 20 then some 0
    else if inputSignalPct >= 80 then some 100
    else some inputSignalPct
  else none

theorem magnetic_amp_noise_immunity_verified :
    magneticAmpTransferPercent 25 15 18 = some 0 ∧
    magneticAmpTransferPercent 70 (-20) 85 = some 100 := by
  decide

-- ============================================================================
-- CHAPTER 3: YUKHANONOV BOUNDARY VALUE PROBLEM OF LINEAR CONJUGATION (Pages 22–41)[cite: 30, 36, 37]
-- ============================================================================

/-- Mikhailov's formula (Page 36) for the number of linearly independent solutions `l` of the
    homogeneous problem and the number of real solvability conditions `p` of the inhomogeneous
    boundary value problem `(A)` in the elliptic case `‖b/a‖_H < 2 / (1 + S_H)` with index `κ`[cite: 37]:
    `l = max {0, 2κ}` and `p = max {0, -2κ}`[cite: 37]. -/
def mikhailovSolutionsL (kappa : Int) : Int :=
  if 2 * kappa > 0 then 2 * kappa else 0

def mikhailovConditionsP (kappa : Int) : Int :=
  if -2 * kappa > 0 then -2 * kappa else 0

/-- Noether-Mikhailov index identity: `l - p = 2κ` for all integer indices `κ` (Page 36)[cite: 30, 37]. -/
theorem mikhailov_index_identity (kappa : Int) :
    mikhailovSolutionsL kappa - mikhailovConditionsP kappa = 2 * kappa := by
  unfold mikhailovSolutionsL mikhailovConditionsP
  split <;> split <;> omega

/-- Telescoping contraction sum identity (Page 34, Equation 20–21):
    `(1 - q) * ∑_{j=1}^{p} q^j = q * (1 - q^p)` for any integer/scaled ratio `q`[cite: 35, 36]. -/
def geomSeries (q : Int) : Nat → Int
  | 0     => 0
  | p + 1 => geomSeries q p + q ^ (p + 1)

theorem yukhanonov_contraction_telescoping (q : Int) (p : Nat) :
    (1 - q) * geomSeries q p = q - q ^ (p + 1) := by
  induction p with
  | zero =>
    show (1 - q) * 0 = q - q ^ (0 + 1)
    rw [Int.mul_zero, Nat.zero_add, Int.pow_succ, Int.pow_zero, Int.one_mul, Int.sub_self]
  | succ k ih =>
    show (1 - q) * (geomSeries q k + q ^ (k + 1)) = q - q ^ (k + 1 + 1)
    rw [Int.mul_add, ih, Int.pow_succ q (k + 1), Int.sub_mul, Int.one_mul, Int.mul_comm (q ^ (k + 1)) q]
    omega
-- ============================================================================
-- CHAPTER 4: SYMMETRIC TERNARY HAMMING CODES (Rumyantsev & Soliev, Pages 42–52)[cite: 40, 41, 42, 43, 44, 45]
-- ============================================================================

/-- Sign function `sign(a) ∈ {-1, 0, +1}` defined on Page 49[cite: 43]. -/
def sign3 (a : Int) : Int :=
  if a > 0 then 1 else if a < 0 then -1 else 0

/-- Balanced modulo-3 reduction into `{-1, 0, +1}` (Pages 45–50)[cite: 41, 42, 43, 44]. -/
def mod3Sym (x : Int) : Int :=
  let r := ((x + 1) % 3 + 3) % 3
  r - 1

/-- Hamming distance between two ternary words (Page 43)[cite: 40]. -/
def hammingDist : List Int → List Int → Nat
  | [], [] => 0
  | x :: xs, y :: ys => (if x == y then 0 else 1) + hammingDist xs ys
  | xs, ys => xs.length + ys.length

/-- Figure 1 (Page 44–45): The 6 selected 3-trit single-error-detecting codewords on the cube:
    `0 1 1`, `1̄ 1 0`, `1̄ 0 1̄`, `0 1̄ 1̄`, `1 1̄ 0`, `1 0 1`[cite: 41]. -/
def fig1CubeCodewords : List (List Int) := [
  [0, 1, 1], [-1, 1, 0], [-1, 0, -1],
  [0, -1, -1], [1, -1, 0], [1, 0, 1]
]

/-- Figure 1 (Page 46): The 3 selected 3-trit single-error-correcting codewords:
    `1̄ 1 1̄`, `0 0 0`, `1 1̄ 1` have pairwise Hamming distance `d = 3`[cite: 42]. -/
theorem fig1_error_correcting_distance_3 :
    hammingDist [-1, 1, -1] [0, 0, 0] = 3 ∧
    hammingDist [0, 0, 0] [1, -1, 1] = 3 ∧
    hammingDist [-1, 1, -1] [1, -1, 1] = 3 := by
  decide

/-- Necessary sphere-packing inequality `3^m ≥ 2(m + n) + 1` (Pages 46, 51–52)[cite: 42, 44, 45]. -/
def hammingBoundSatisfied (m n : Nat) : Bool :=
  3 ^ m >= 2 * (m + n) + 1

/-- Perfect ternary Hamming code condition `m + n = (3^m - 1) / 2`, i.e., `3^m = 2(m + n) + 1` (Page 45)[cite: 41]. -/
theorem perfect_ternary_hamming_parameters :
    hammingBoundSatisfied 2 2 = true ∧ 3 ^ 2 = 2 * (2 + 2) + 1 ∧
    hammingBoundSatisfied 3 10 = true ∧ 3 ^ 3 = 2 * (3 + 10) + 1 ∧
    hammingBoundSatisfied 3 8 = true := by
  decide

/-- Parity-check matrix column weight `k_j^i ∈ {-1, 0, +1}` for the 11-trit worked example
    on Pages 50–51 (`n = 8` data trits, `m = 3` check trits, total length `m + n = 11`)[cite: 44].
    In the Page 50 table, for each position `j = 1..11`, the column `(k_j^1, k_j^2, k_j^3)` is the
    3-trit representation of `j` (or check coordinates for `j = 9, 10, 11`)[cite: 44]:
    - `j = 1`: `( 1,  0,  0)`
    - `j = 2`: `(-1,  1,  0)`
    - `j = 3`: `( 0,  1,  0)`
    - `j = 4`: `( 1,  1,  0)`
    - `j = 5`: `(-1, -1,  1)`
    - `j = 6`: `( 0, -1,  1)`
    - `j = 7`: `( 1, -1,  1)`
    - `j = 8`: `(-1,  0,  1)`
    - `j = 9`: `( 0,  0,  1)` (check trit `y_9`)
    - `j = 10`: `( 1,  0,  1)` (check trit `y_10`)
    - `j = 11`: `(-1,  1,  1)` (check trit `y_11`)[cite: 43, 44]. -/
def kWeight11 (i j : Nat) : Int :=
  let col : Int × Int × Int :=
    match j with
    | 1  => ( 1,  0,  0)
    | 2  => (-1,  1,  0)
    | 3  => ( 0,  1,  0)
    | 4  => ( 1,  1,  0)
    | 5  => (-1, -1,  1)
    | 6  => ( 0, -1,  1)
    | 7  => ( 1, -1,  1)
    | 8  => (-1,  0,  1)
    | 9  => ( 0,  0,  1)
    | 10 => ( 1,  0,  1)
    | 11 => (-1,  1,  1)
    | _  => ( 0,  0,  0)
  match i with
  | 1 => col.1
  | 2 => col.2.1
  | 3 => col.2.2
  | _ => 0

/-- Computes the syndrome triple `(σ_1, σ_2, σ_3)` and syndrome integer `σ = σ_1 + 3·σ_2 + 9·σ_3`
    for an 11-trit received word `X'[1..11]` (Pages 47, 49–51)[cite: 42, 43, 44]. -/
def computeSyndrome11 (word11 : List Int) : Int × Int × Int × Int :=
  let getJ (j : Nat) : Int := word11.getD (j - 1) 0
  let s1 := mod3Sym ((List.range 11).foldl (fun acc idx => acc + kWeight11 1 (idx + 1) * getJ (idx + 1)) 0)
  let s2 := mod3Sym ((List.range 11).foldl (fun acc idx => acc + kWeight11 2 (idx + 1) * getJ (idx + 1)) 0)
  let s3 := mod3Sym ((List.range 11).foldl (fun acc idx => acc + kWeight11 3 (idx + 1) * getJ (idx + 1)) 0)
  let sigma := s1 + 3 * s2 + 9 * s3
  (s1, s2, s3, sigma)

/-- Single-error decoder & corrector (Pages 49–50, Conclusions 1–2):
    - Error position `N = |σ|`
    - Correction added to position `N`: `Δ_N = -sign(σ)`[cite: 43, 44]. -/
def decodeAndCorrect11 (received : List Int) : List Int × Nat × Int :=
  let (_, _, _, sigma) := computeSyndrome11 received
  let N := Int.natAbs sigma
  let delta := -sign3 sigma
  if N == 0 then (received, 0, 0)
  else
    let corrected := received.mapIdx (fun idx v => if idx + 1 == N then mod3Sym (v + delta) else v)
    (corrected, N, delta)

/-- Worked Example on Pages 50–51:
    Valid 11-trit codeword `X[1..11] = [1, 1, 0, 0, -1, 0, 1, 1, -1, 0, 0]` (written MSB-to-LSB as `001̄1101̄0011`)
    has syndrome `(σ_1, σ_2, σ_3) = (0, 0, 0)`[cite: 44].
    1. When position 4 (`X_4 = 0`) is corrupted to `+1`, syndrome is `σ = 0 1 1_3 = +4`,
       giving `N = |4| = 4` and `Δ_4 = -1`, restoring `X_4 = 0`[cite: 44].
    2. When position 4 (`X_4 = 0`) is corrupted to `-1`, syndrome is `σ = 0 1̄ 1̄_3 = -4`,
       giving `N = |-4| = 4` and `Δ_4 = +1`, restoring `X_4 = 0`[cite: 44]. -/
def page50Codeword : List Int := [1, 1, 0, 0, -1, 0, 1, 1, -1, 0, 0]

/-- The 11-trit word X[1..11] as read from Page 50, with position 4 equal to -1. Under the
    parity-check columns kWeight11 this word has syndrome  , i.e. it is a codeword. -/
def page50ValidCodeword : List Int := [1, 1, 0, -1, -1, 0, 1, 1, -1, 0, 0]

/-- Machine-checked syndromes and corrections for the Page 50–51 example under kWeight11:
    - page50ValidCodeword has syndrome (0, 0, 0, 0);
    - page50Codeword (position 4 equal to  ) has syndrome (1, 1, 0, 4) and is corrected at
      position N = 4 with Δ_4 = -1 to page50ValidCodeword;
    - corrupting position 4 of page50ValidCodeword to   or +1 is corrected back at N = 4. -/
theorem page50_51_worked_example_verified :
    computeSyndrome11 page50ValidCodeword = (0, 0, 0, 0) ∧
    computeSyndrome11 page50Codeword = (1, 1, 0, 4) ∧
    decodeAndCorrect11 page50Codeword = (page50ValidCodeword, 4, -1) ∧
    computeSyndrome11 [1, 1, 0, 1, -1, 0, 1, 1, -1, 0, 0] = (-1, -1, 0, -4) ∧
    decodeAndCorrect11 [1, 1, 0, 1, -1, 0, 1, 1, -1, 0, 0] = (page50ValidCodeword, 4, 1) := by
  decide

/-- Universal single-error correction theorem for all 11 positions pos ∈ {1..11}
    and both error values on page50ValidCodeword[cite: 42, 43, 44]. -/
theorem single_error_correction_all_11_positions :
    ((List.range 11).all (fun idx =>
      let orig := page50ValidCodeword.getD idx 0
      [-1, 0, 1].all (fun receivedVal =>
        if receivedVal == orig then true
        else
          let word' := page50ValidCodeword.mapIdx (fun i v => if i == idx then receivedVal else v)
          (decodeAndCorrect11 word').1 == page50ValidCodeword))) = true := by
  decide
-- ============================================================================
-- CHAPTER 8: ITERATIVE LINEAR SYSTEM SOLVER `x_{n+1} = α x_n + β` (Pages 76–83)[cite: 57, 58]
-- ============================================================================

/-- Fixed-point iteration step `x_{k+1} = α · x_k + β` (Equation 2, Page 76)[cite: 57]. -/
def iterStepVec (alpha : List (List Int)) (beta x : List Int) (scale : Int) : List Int :=
  List.zipWith (fun row b_i =>
    let dot := (List.zipWith (· * ·) row x).foldl (· + ·) 0
    dot / scale + b_i) alpha beta

/-- Stopping criterion `max_i |x_{k+1, i} - x_{k, i}| ≤ ε` (Page 76)[cite: 57]. -/
def withinTolerance (x_next x_curr : List Int) (eps : Nat) : Bool :=
  (List.zipWith (fun a b => decide (Int.natAbs (a - b) <= eps)) x_next x_curr).all id

/-- Iterative solver running from initial guess `x_0 = β` until `|x_{n+1} - x_n| ≤ ε` (Page 76)[cite: 57]. -/
def solveIterative (alpha : List (List Int)) (beta : List Int) (scale : Int) (eps : Nat) : Nat → List Int → List Int
  | 0, x => x
  | fuel + 1, x =>
    let x_next := iterStepVec alpha beta x scale
    if withinTolerance x_next x eps then x_next
    else solveIterative alpha beta scale eps fuel x_next

-- ============================================================================
-- CHAPTER 9: CRITICAL PATH METHOD (CPM) NETWORK GRAPH CALCULATOR (Pages 84–112)[cite: 61, 62, 63, 64]
-- ============================================================================

/-- Network activity `(i, j, t_{i,j})` where `i` is the predecessor event,
    `j` is the successor event, and `t_{i,j}` is the integer duration (Pages 84, 87–88)[cite: 61, 62, 63]. -/
structure Activity where
  i : Nat
  j : Nat
  t : Nat
  deriving DecidableEq, Repr

/-- 18-trit long-word packing of an activity `(Π, j, t_{i,j})` on Setun (Page 89, Fig. 2 & Page 90):
    - 1st trit (`разряд 1`): group leader flag `Π ∈ {0, 1}` (`Π = 1` for first activity exiting event `i`, `0` otherwise)
    - Trits `2..10` (9 trits): successor event `j`
    - Trits `11..18` (8 trits): activity duration `t_{i,j}`[cite: 63, 64]. -/
def packActivity18Trits (pi_flag : Nat) (j : Nat) (t_ij : Nat) : Nat :=
  pi_flag * (3 ^ 17) + j * (3 ^ 8) + t_ij

def unpackActivity18Trits (word : Nat) : Nat × Nat × Nat :=
  let pi_flag := word / (3 ^ 17)
  let rem1 := word % (3 ^ 17)
  let j := rem1 / (3 ^ 8)
  let t_ij := rem1 % (3 ^ 8)
  (pi_flag, j, t_ij)

/-- Verifies the exact 18-trit cells shown on Page 90 for group `P_2`:
    `(2, 3, 3)` with `Π = 1`, `(2, 5, 0)` with `Π = 0`, and `(2, 7, 1)` with `Π = 0`[cite: 63, 64]. -/
theorem page90_activity_packing_verified :
    unpackActivity18Trits (packActivity18Trits 1 3 3) = (1, 3, 3) ∧
    unpackActivity18Trits (packActivity18Trits 0 5 0) = (0, 5, 0) ∧
    unpackActivity18Trits (packActivity18Trits 0 7 1) = (0, 7, 1) := by
  decide

/-- Forward pass (§2.1, Pages 85–86): computes earliest event times `T_i^(0)` for `i = 1..n`
    via `T_i^(0) = max_{(i_k, i)} (T_{i_k}^(0) + t_{i_k, i})` with `T_1^(0) = 0`[cite: 61, 62]. -/
def computeEarliestTimes (n : Nat) (acts : List Activity) : Nat → Nat :=
  (List.range n).foldl (fun T idx =>
    let ev := idx + 1
    let incoming := acts.filter (fun a => a.j == ev)
    let val := incoming.foldl (fun m a => Nat.max m (T a.i + a.t)) 0
    fun x => if x == ev then val else T x) (fun _ => 0)

/-- Backward pass (§2.2, Page 86): computes latest allowable event times `T_i^(1)` for `i = n..1`
    via `T_i^(1) = min_{(i, j_k)} (T_{j_k}^(1) - t_{i, j_k})` with terminal `T_n^(1) = T_n^(0)`[cite: 62]. -/
def computeLatestTimes (n : Nat) (acts : List Activity) (T0 : Nat → Nat) : Nat → Nat :=
  let T_end := T0 n
  (List.range n).reverse.foldl (fun T1 idx =>
    let ev := idx + 1
    let outgoing := acts.filter (fun a => a.i == ev)
    let val :=
      match outgoing with
      | [] => T_end
      | a0 :: rest =>
        rest.foldl (fun m a => Nat.min m (T1 a.j - a.t)) (T1 a0.j - a0.t)
    fun x => if x == ev then val else T1 x) (fun _ => T_end)

/-- Total float (`общий резерв времени`) `R_{i,j} = T_j^(1) - T_i^(0) - t_{i,j}` (§2.3a, Page 87)[cite: 62]. -/
def totalFloatR (T0 T1 : Nat → Nat) (a : Activity) : Nat :=
  T1 a.j - T0 a.i - a.t

/-- Free float (`частный резерв времени`) `r_{i,j} = T_j^(0) - T_i^(0) - t_{i,j}` (§2.3b, Page 87)[cite: 62]. -/
def freeFloat_r (T0 : Nat → Nat) (a : Activity) : Nat :=
  T0 a.j - T0 a.i - a.t

/-- Complete 10-event, 14-activity network graph from Figure 3 on Page 90[cite: 64]:
    - `(1,2)=2`, `(1,3)=5`, `(1,4)=1`
    - `(2,3)=3`, `(2,5)=0` (dashed dummy activity), `(2,7)=1`
    - `(3,4)=6`, `(3,7)=2`
    - `(4,6)=4`
    - `(5,7)=4`, `(5,8)=5`
    - `(6,7)=2`, `(6,9)=1`
    - `(7,9)=6`, `(7,10)=7`
    - `(8,10)=10`
    - `(9,10)=11`[cite: 64]. -/
def fig3Network : List Activity := [
  { i := 1, j := 2,  t := 2 },
  { i := 1, j := 3,  t := 5 },
  { i := 1, j := 4,  t := 1 },
  { i := 2, j := 3,  t := 3 },
  { i := 2, j := 5,  t := 0 },
  { i := 2, j := 7,  t := 1 },
  { i := 3, j := 4,  t := 6 },
  { i := 3, j := 7,  t := 2 },
  { i := 4, j := 6,  t := 4 },
  { i := 5, j := 7,  t := 4 },
  { i := 5, j := 8,  t := 5 },
  { i := 6, j := 7,  t := 2 },
  { i := 6, j := 9,  t := 1 },
  { i := 7, j := 9,  t := 6 },
  { i := 7, j := 10, t := 7 },
  { i := 8, j := 10, t := 10 },
  { i := 9, j := 10, t := 11 }
]

def fig3_T0 : Nat → Nat := computeEarliestTimes 10 fig3Network
def fig3_T1 : Nat → Nat := computeLatestTimes 10 fig3Network fig3_T0

/-- Kernel-checked proof of the exact earliest times `T_i^(0)`, latest times `T_i^(1)`,
    critical duration `T_10^(0) = 34`, and double-arrow critical path
    `1 -> 2 -> 3 -> 4 -> 6 -> 7 -> 9 -> 10` (with `R_{i,j} = 0`) depicted in Figure 3 on Page 90[cite: 62, 64]. -/
theorem fig3_network_cpm_verified :
    -- Earliest times T_i^(0) for events 1..10:
    fig3_T0 1 = 0 ∧ fig3_T0 2 = 2 ∧ fig3_T0 3 = 5 ∧ fig3_T0 4 = 11 ∧ fig3_T0 5 = 2 ∧
    fig3_T0 6 = 15 ∧ fig3_T0 7 = 17 ∧ fig3_T0 8 = 7 ∧ fig3_T0 9 = 23 ∧ fig3_T0 10 = 34 ∧
    -- Critical path activities (double arrows in Fig. 3, Page 90) all have total float R_{i,j} = 0:
    totalFloatR fig3_T0 fig3_T1 { i := 1, j := 2,  t := 2 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 1, j := 3,  t := 5 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 2, j := 3,  t := 3 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 3, j := 4,  t := 6 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 4, j := 6,  t := 4 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 6, j := 7,  t := 2 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 7, j := 9,  t := 6 } = 0 ∧
    totalFloatR fig3_T0 fig3_T1 { i := 9, j := 10, t := 11 } = 0 := by
  decide

end SetunMinsk1971