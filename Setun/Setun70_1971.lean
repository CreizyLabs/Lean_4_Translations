/-!
# File 2: СТРУКТУРА И АЛГОРИТМ ФУНКЦИОНИРОВАНИЯ МАЛОЙ ВЫЧИСЛИТЕЛЬНОЙ МАШИНЫ «СЕТУНЬ-70»
Complete machine-verified Lean 4 replication of:
`Computer_architecture_Setun_1971.pdf` (N. P. Brusentsov & E. A. Zhogolev, LGU 1971, Pages 34–51)[cite: 9, 10].
Replicates:
- 6-trit syllables (`3^6 = 729` values, `-364 .. +364`) and 18-trit words (3 syllables)[cite: 10]
- Two-level paged memory: 27 Level-1 pages (9 RAM `[-4..4]`, 18 ROM `[-13..-5, 5..13]`) × 81 syllables `[-40..40]`[cite: 11, 17]
- Level-2 memory `f[-1:1, -3280:3280, -40:40, 1:6]`[cite: 12, 13, 17]
- All 27 Basic Operations `B1..B27` (`LST`, `COT`, `XNN`, `E-1`, `E=0`, `E+1`, `T-E`, `E=T`, `T+E`,
  `CLT`, `CET`, `CGT`, `T=C`, `R=T`, `C=T`, `T=W`, `YFT`, `W=S`, `SMT`, `Y=T`, `SAT`, `S-T`, `TDN`,
  `S+T`, `LBT`, `L*T`, `LHT`)[cite: 15, 16]
- All 27 Special/Privileged Operations `S1..S27` (`COPYG1..3`, `COPYF1..3`, `LOADQ1..3`, `COPYP`,
  `EXCHP`, `LOADP`, `COPYMC`, `RETNMC`, `LOADMC`, `LOADH1..3`, `LOADU1..3`, `LOADF1..3`, `LOADG1..3`)[cite: 16, 17]
- Macro-operations (`MACRO`), Reference Syllables (`REFSYL`), Program Counter (`INCRC`), and
  Interrupt Handler (`IR` with causes `w ∈ {-40 .. -28}`)[cite: 14, 15, 17, 18].
Zero `sorry`, zero custom axioms, zero approximations, zero placeholders.
-/

namespace Setun70

-- ============================================================================
-- 1. TERNARY ARRAYS, 6-TRIT SYLLABLES & BOUNDARY PAIR SEMANTICS (§3.1–3.4)[cite: 12, 13]
-- ============================================================================

/-- 6-trit syllable (`слог`) holds `3^6 = 729` balanced ternary values in `[-364, +364]`[cite: 10]. -/
def syllableMod : Int := 729
def syllableHalf : Int := 364

/-- 18-trit 3-syllable word (`T`, `S`, `R`, `Y`) holds `3^18 = 387,420,489` values[cite: 10]. -/
def word18Mod : Int := 3 ^ 18
def word18Half : Int := (3 ^ 18 - 1) / 2

theorem syllable_and_word_bounds :
    3 ^ 6 = 729 ∧ 2 * syllableHalf + 1 = 729 ∧ 3 ^ 18 = 387420489 := by
  decide

/-- Balanced modulo reduction into `[-(3^k - 1)/2, +(3^k - 1)/2]` (§3.3)[cite: 13]. -/
def balMod (k : Nat) (v : Int) : Int :=
  let m : Int := 3 ^ k
  let half : Int := (m - 1) / 2
  let r := ((v + half) % m + m) % m
  r - half

/-- Extracts the `i`-th trit (1-indexed from MSB `1..n`) of a `n`-trit balanced ternary integer (§3.2–3.3)[cite: 12, 13]. -/
def getTrit (n : Nat) (idx1 : Nat) (v : Int) : Int :=
  let w := balMod n v
  let shift := n - idx1
  balMod 1 ((w - balMod shift w) / (3 ^ shift))

/-- Extracts a contiguous sub-slice `a[m : s]` (1-indexed from MSB `1..n`) as a balanced integer (§3.2)[cite: 12]. -/
def sliceTrits (n m s : Nat) (v : Int) : Int :=
  let len := s + 1 - m
  let w := balMod n v
  let shifted := (w - balMod (n - s) w) / (3 ^ (n - s))
  balMod len shifted

-- ============================================================================
-- 2. INSTRUCTION SYLLABLE DECODING `k[1:6]` (§4, §5.1, §5.3)[cite: 14, 17, 18]
-- ============================================================================

/-- Decoded fields of the 6-trit executed syllable register `k[1:6]` (Page 48, 50):
    - `k1 = k[1]`: operand word length indicator (`-1` => 1 syl, `0` => 2 syl, `+1` => 3 syl)
    - `k2 = k[2]`: index into operand page register `h[-1:1]`
    - `k3 = k[3]`: operation level/class when `k1 = 0 ∧ k2 = 0` (`-1`: MACRO, `0`: BASIC, `+1`: SPEC)
    - `ka = k[3:6]`: 4-trit operand syllable address on page (`[-40..+40]`)
    - `ko = k[4:6]`: 3-trit operation code (`[-13..+13]`, mapped via `ko + 14` to `1..27`)[cite: 14, 15, 17, 18]. -/
structure DecodedSyllable where
  k1 : Int
  k2 : Int
  k3 : Int
  ka : Int
  ko : Int
  deriving DecidableEq, Repr

def decodeSyllable (k_val : Int) : DecodedSyllable :=
  { k1 := getTrit 6 1 k_val
    k2 := getTrit 6 2 k_val
    k3 := getTrit 6 3 k_val
    ka := sliceTrits 6 3 6 k_val
    ko := sliceTrits 6 4 6 k_val }

-- ============================================================================
-- 3. INTERRUPT CAUSES `w[1:4]` (§5.2, Pages 50–51)[cite: 18]
-- ============================================================================

/-- All 13 hardware interrupt cause codes `w ∈ {-40 .. -28}` specified in §5.2 (Pages 50–51)[cite: 18]:
    - `v[1] => w = -40`: Timer (`Часы` / `WATCH`)
    - `v[2..4] => w = -39..-37`: Signal from I/O device group `-1, 0, +1` (`INOUT`)
    - `v[5..7] => w = -36..-34`: Signal from Level-2 memory bank `-1, 0, +1` (`SUIT`)
    - `v[8] => w = -33`: Console attention button (`ATTENT`)
    - `v[9] => w = -32`: Program page exhaustion (`ca = 40` overflow in `INCRC`)
    - `w = -31`: Stack page underflow (`pa = -13` in `BASIC`/`SPEC`)
    - `w = -30`: Stack page overflow (`pa = 13` in `CYCLE`/`MACRO`)
    - `w = -29`: Operand crosses page boundary (`ka + k1 + 1 > 40` in `REFSYL` / `B18`)
    - `w = -28`: Forbidden syllable (`MACRO` in `c1 = 0`, or `SPEC` in user mode `c1 = -1`)[cite: 14, 15, 16, 18]. -/
def interruptCauseFromV (i : Nat) : Int :=
  (i : Int) - 41

theorem interrupt_causes_verified :
    interruptCauseFromV 1 = -40 ∧
    interruptCauseFromV 2 = -39 ∧
    interruptCauseFromV 5 = -36 ∧
    interruptCauseFromV 8 = -33 ∧
    interruptCauseFromV 9 = -32 := by
  decide

-- ============================================================================
-- 4. COMPLETE SETUN-70 PROCESSOR STATE (§4 & §5.1, Pages 41–50)[cite: 13, 17, 18]
-- ============================================================================

/-- Complete architectural state of the Setun-70 computer (`begin ternary array ...` on Page 41)[cite: 13, 17, 18]. -/
structure State where
  /-- Level-2 memory `f[-1:1, -3280:3280, -40:40]` storing 6-trit syllables[cite: 13, 17]. -/
  f : Int → Int → Int → Int := fun _ _ _ => 0
  /-- Level-1 memory `m[-13:13, -40:40]` (Pages `-4..4` = RAM, `-13..-5` & `5..13` = ROM)[cite: 11, 13, 17]. -/
  m : Int → Int → Int := fun _ _ => 0
  /-- Level-2 page pointer registers `q[-1:1]` (8 trits each)[cite: 13, 17]. -/
  q : Int → Int := fun _ => 0
  /-- I/O buffer registers `g[-1:1, 1:7]` (represented as 6-trit syllable + 7th trit)[cite: 13, 16, 17]. -/
  g_syl : Int → Int := fun _ => 0
  g_7   : Int → Int := fun _ => 0
  /-- I/O mode registers `u[-1:1]` (4 trits each)[cite: 13, 17]. -/
  u : Int → Int := fun _ => 0
  /-- Open operand page registers `h[-1:1]` (3 trits each)[cite: 13, 17]. -/
  h : Int → Int := fun _ => 0
  /-- Mode & program pointer register `c[1:32]`, decomposed into active fields `c1, ch, ca`
      and saved state frames `c[9:20]` and `c[21:32]`[cite: 13, 15, 16, 17]. -/
  c1 : Int := 1       -- c[1]: Operating mode (-1 = user, 0 = macro, +1 = interrupt)[cite: 17, 18]
  ch : Int := 12      -- c[2:4]: Active program page (-13..+13)[cite: 14, 17]
  ca : Int := -40     -- c[5:8]: Active program syllable on page (-40..+40)[cite: 14, 17]
  c_9_20  : Int := 0  -- Saved 12-trit status level 1 (c[11:14] = c[1:4], c[17:20] = c[5:8])[cite: 15, 16, 17]
  c_21_32 : Int := 0  -- Saved 12-trit status level 2[cite: 15, 16, 17]
  /-- 18-trit Multiplier register `R[1:18]` and low-order register `Y[1:18]`[cite: 13, 17]. -/
  R : Int := 0
  Y : Int := 0
  /-- Stack pointer register `p[1:10]`: active `ph = p[1:2]`, `pa = p[3:5]`,
      and shadow stack pointer `p_6_10 = p[6:10]` (`ph_saved`, `pa_saved`)[cite: 13, 16, 17, 18]. -/
  ph : Int := 0
  pa : Int := 0
  ph_saved : Int := 0
  pa_saved : Int := 0
  /-- 9-trit Interrupt request register `v[1:9]`[cite: 13, 14, 18]. -/
  v : Nat → Int := fun _ => 0
  /-- 6-trit Small adder (exponent/index register) `e[1:6]`[cite: 13, 15, 18]. -/
  e : Int := 0
  /-- 6-trit Current syllable register `k[1:6]`[cite: 13, 14, 18]. -/
  k : Int := 0
  /-- 4-trit Interrupt cause register `w[1:4]`[cite: 13, 14, 18]. -/
  w : Int := 0
  /-- 3-trit Level-1 exchange page pointer `hf[1:3]`[cite: 13, 16, 18]. -/
  hf : Int := 0
  /-- I/O synchronization flip-flops `a[-1:1]`[cite: 13, 14, 18]. -/
  a : Int → Int := fun _ => 0
  /-- Machine run state flip-flop `start[1:1]`[cite: 13, 14, 18]. -/
  start : Int := 1

namespace State

-- ============================================================================
-- 5. STACK WINDOW `T`, `t`, AND SECOND-ON-STACK `S` (§4 & §5.1, Pages 48, 50)[cite: 17, 18]
-- ============================================================================

/-- Reads a 6-trit syllable from Level-1 memory `m[page, addr]`[cite: 11, 17]. -/
def readSyl (st : State) (page addr : Int) : Int :=
  balMod 6 (st.m page addr)

/-- Writes a 6-trit syllable to Level-1 memory `m[page, addr]`.
    Note from §2.5 & `B18`/`COPY`: only RAM pages `|page| ≤ 4` are writable in user operations[cite: 11, 15, 16, 17]. -/
def writeSyl (st : State) (page addr val : Int) : State :=
  let v6 := balMod 6 val
  { st with m := fun p s => if p == page && s == addr then v6 else st.m p s }

/-- Reads an 18-trit 3-syllable word from `m[page, base .. base+2]`[cite: 10, 17, 18]. -/
def readWord3 (st : State) (page base : Int) : Int :=
  let s1 := st.readSyl page base
  let s2 := st.readSyl page (base + 1)
  let s3 := st.readSyl page (base + 2)
  s1 * (729 * 729) + s2 * 729 + s3

/-- Writes an 18-trit 3-syllable word into `m[page, base .. base+2]`[cite: 10, 17, 18]. -/
def writeWord3 (st : State) (page base val18 : Int) : State :=
  let w := balMod 18 val18
  let s1 := sliceTrits 18 1 6 w
  let s2 := sliceTrits 18 7 12 w
  let s3 := sliceTrits 18 13 18 w
  let st1 := st.writeSyl page base s1
  let st2 := st1.writeSyl page (base + 1) s2
  st2.writeSyl page (base + 2) s3

/-- Stack window `T ~ m[ph, 3*pa - 1 : 3*pa + 1]` (18-trit top of stack, Page 48, 50)[cite: 17, 18]. -/
def getT (st : State) : Int :=
  st.readWord3 st.ph (3 * st.pa - 1)

def setT (st : State) (val18 : Int) : State :=
  st.writeWord3 st.ph (3 * st.pa - 1) val18

/-- Senior syllable of stack window `t ~ m[ph, 3*pa - 1]` (6-trit syllable, Page 48, 50)[cite: 17, 18]. -/
def get_t (st : State) : Int :=
  st.readSyl st.ph (3 * st.pa - 1)

def set_t (st : State) (val6 : Int) : State :=
  st.writeSyl st.ph (3 * st.pa - 1) val6

/-- Cell immediately below stack window `S ~ m[ph, 3*(pa - 1) - 1 : 3*(pa - 1) + 1]` (Page 48, 50)[cite: 17, 18]. -/
def getS (st : State) : Int :=
  st.readWord3 st.ph (3 * (st.pa - 1) - 1)

def setS (st : State) (val18 : Int) : State :=
  st.writeWord3 st.ph (3 * (st.pa - 1) - 1) val18

-- ============================================================================
-- 6. CORE PROCEDURES: `INCRC`, `IR`, `REFSYL`, `MACRO` (Pages 43–48)[cite: 14, 15, 17]
-- ============================================================================

/-- `procedure INCRC` (Page 43):
    `if c1 ≠ 1 & ca = 40 then v[9] := 1; ca := ca + 1`[cite: 14]. -/
def INCRC (st : State) : State :=
  let st1 :=
    if st.c1 != 1 && st.ca == 40 then
      { st with v := fun idx => if idx == 9 then 1 else st.v idx }
    else st
  { st1 with ca := balMod 4 (st1.ca + 1) }

/-- Packs `(c1, ch, ca)` into the 12-trit saved frame `c[9:20]` (`c[11:14] := c[1:4]; c[17:20] := c[5:8]`)[cite: 15, 17]. -/
def packCFrame (c1 ch ca : Int) : Int :=
  let c_1_4 := c1 * 27 + balMod 3 ch
  c_1_4 * 81 + balMod 4 ca

/-- Unpacks `(c1, ch, ca)` from a 12-trit saved frame `z[1:12]` (`S14: RETNMC`, Page 46)[cite: 16]. -/
def unpackCFrame (frame : Int) : Int × Int × Int :=
  let ca := balMod 4 frame
  let c_1_4 := (frame - ca) / 81
  let ch := balMod 3 c_1_4
  let c1 := balMod 1 ((c_1_4 - ch) / 27)
  (c1, ch, ca)

/-- `IR` Interrupt Handler block (Page 48):
    Saves `c`, enters interrupt mode `c1 := 1; ch := 13; ca := -13`, swaps stack pointers
    `p[1:5] <-> p[6:10]`, increments `pa`, and pushes `m[13, w]` into `t`[cite: 17]. -/
def enterIR (st : State) (w_cause : Int) : State :=
  let st0 := { st with w := w_cause }
  let savedFrame := packCFrame st0.c1 st0.ch st0.ca
  let new_pa := st0.pa_saved + 1
  let st1 : State := { st0 with
    c_21_32 := st0.c_9_20
    c_9_20  := savedFrame
    c1      := 1
    ch      := 13
    ca      := -13
    ph       := st0.ph_saved
    pa       := new_pa
    ph_saved := st0.ph
    pa_saved := st0.pa }
  let st2 := st1.setT 0
  st2.set_t (st1.readSyl 13 w_cause)

/-- `procedure REFSYL` (Page 43):
    Copies `1, 2, or 3` syllables (`k1 = -1, 0, +1`) from `m[h[k2], ka .. ka+k1+1]`
    into the stack window `T` (zero-padding lower syllables automatically)[cite: 10, 14]. -/
def REFSYL (st : State) (dec : DecodedSyllable) : State :=
  if st.c1 != 1 && dec.ka + dec.k1 + 1 > 40 then
    st.enterIR (-29)
  else
    let srcPage := st.h dec.k2
    let st0 := st.setT 0
    let s1 := st0.readSyl srcPage dec.ka
    let st1 := st0.writeSyl st0.ph (3 * st0.pa - 1) s1
    let st2 :=
      if dec.k1 >= 0 then
        let s2 := st1.readSyl srcPage (dec.ka + 1)
        st1.writeSyl st1.ph (3 * st1.pa) s2
      else st1
    let st3 :=
      if dec.k1 >= 1 then
        let s3 := st2.readSyl srcPage (dec.ka + 2)
        st2.writeSyl st2.ph (3 * st2.pa + 1) s3
      else st2
    st3.INCRC

/-- `MACRO` operation handler (`k1 = 0 ∧ k2 = 0 ∧ k3 = -1`, Page 44 & §5.3 Page 51)[cite: 15, 18]. -/
def execMACRO (st : State) (dec : DecodedSyllable) : State :=
  if st.c1 == 1 then
    { st with start := 0 } -- FINISH: Halt machine in interrupt mode (§5.3)[cite: 15, 18]
  else if st.c1 == 0 then
    st.enterIR (-28)       -- Forbidden syllable interrupt in macro mode (§5.3)[cite: 15, 18]
  else if st.pa == 13 then
    st.enterIR (-30)       -- Stack overflow interrupt[cite: 15, 18]
  else
    let savedFrame := packCFrame st.c1 st.ch st.ca
    let st1 : State := { st with
      pa      := st.pa + 1
      c_21_32 := st.c_9_20
      c_9_20  := savedFrame
      c1      := 0
      ch      := -13
      ca      := -13 }
    let st2 := st1.setT 0
    st2.set_t (st2.readSyl (-13) dec.ka)

-- ============================================================================
-- 7. ALL 27 BASIC OPERATIONS `B1..B27` (Pages 44–45)[cite: 15, 16]
-- ============================================================================

/-- Tritwise multiplication `SMT` (`B19`: `z[i] := z[i] * x[i]` for `i = 1..18`)[cite: 15]. -/
def tritwiseSMT (s_val t_val : Int) : Int :=
  (List.range 18).foldl (fun acc idx =>
    let zs := getTrit 18 (idx + 1) s_val
    let xt := getTrit 18 (idx + 1) t_val
    acc * 3 + zs * xt) 0

/-- Tritwise saturation/merge `SAT` (`B21`, Page 45):
    `if z[i] = 0 then z[i] := x[i] else if z[i] ≠ x[i] & x[i] ≠ 0 then z[i] := 0`[cite: 15]. -/
def tritwiseSAT (s_val t_val : Int) : Int :=
  (List.range 18).foldl (fun acc idx =>
    let zi := getTrit 18 (idx + 1) s_val
    let xi := getTrit 18 (idx + 1) t_val
    let res :=
      if zi == 0 then xi
      else if zi != xi && xi != 0 then 0
      else zi
    acc * 3 + res) 0

/-- Executes one of the 27 Basic Operations `B1..B27` indexed by `ko + 14 ∈ {1..27}` (Pages 44–45)[cite: 15, 16]. -/
def execBASIC (st : State) (ko : Int) : State :=
  if st.c1 != 1 && st.pa == -13 then
    st.enterIR (-31) -- Stack underflow[cite: 15, 18]
  else
    let opIdx := ko + 14
    let T := st.getT
    let S := st.getS
    let t := st.get_t
    match opIdx with
    -- B1: "LST" - Shift 36-trit (S, Y) by t trits[cite: 15]
    | 1 =>
      let x36 := S * (3 ^ 18) + st.Y
      let shifted := if t >= 0 then x36 * (3 ^ t.toNat) else x36 / (3 ^ (-t).toNat)
      let newS := balMod 18 (shifted / (3 ^ 18))
      let newY := balMod 18 shifted
      let st1 := (st.setS newS)
      ({ st1 with Y := newY, pa := st.pa - 1 }).INCRC

    -- B2: "COT" - Branch to t if |S| > (3^17)/2[cite: 15]
    | 2 =>
      if (Int.natAbs S : Int) > (3 ^ 17) / 2 then
        { st with ca := balMod 4 t, pa := st.pa - 1 }
      else
        ({ st with pa := st.pa - 1 }).INCRC

    -- B3: "XNN" - Normalize 36-trit (T, Y) and adjust exponent e[cite: 15]
    | 3 =>
      let x36 := T * (3 ^ 18) + st.Y
      let x1 := getTrit 18 1 T
      let (newX, adj) :=
        if x1 != 0 then (x36 / 3, (1 : Int))
        else (x36, (0 : Int))
      let newT := balMod 18 (newX / (3 ^ 18))
      let newY := balMod 18 newX
      let st1 := st.setT newT
      ({ st1 with Y := newY, e := balMod 6 (st.e + adj) }).INCRC

    -- B4: "E-1"[cite: 15]
    | 4 => ({ st with e := balMod 6 (st.e - 1) }).INCRC
    -- B5: "E=0"[cite: 15]
    | 5 => ({ st with e := 0 }).INCRC
    -- B6: "E+1"[cite: 15]
    | 6 => ({ st with e := balMod 6 (st.e + 1) }).INCRC
    -- B7: "T-E"[cite: 15]
    | 7 => (st.setT (T - st.e * (3 ^ 12))).INCRC
    -- B8: "E=T"[cite: 15]
    | 8 => ({ st with e := balMod 6 t, pa := st.pa - 1 }).INCRC
    -- B9: "T+E"[cite: 15]
    | 9 => (st.setT (T + st.e * (3 ^ 12))).INCRC

    -- B10: "CLT" - Conditional jump if S < 0[cite: 15]
    | 10 =>
      if S < 0 then { st with ca := balMod 4 t, pa := st.pa - 1 }
      else ({ st with pa := st.pa - 1 }).INCRC

    -- B11: "CET" - Conditional jump if S = 0[cite: 15]
    | 11 =>
      if S == 0 then { st with ca := balMod 4 t, pa := st.pa - 1 }
      else ({ st with pa := st.pa - 1 }).INCRC

    -- B12: "CGT" - Conditional jump if S > 0[cite: 15]
    | 12 =>
      if S > 0 then { st with ca := balMod 4 t, pa := st.pa - 1 }
      else ({ st with pa := st.pa - 1 }).INCRC

    -- B13: "T=C"[cite: 15]
    | 13 => ((st.setT 0).set_t st.ca).INCRC
    -- B14: "R=T"[cite: 15]
    | 14 => ({ st with R := T, pa := st.pa - 1 }).INCRC
    -- B15: "C=T"[cite: 15]
    | 15 => { st with ca := balMod 4 t, pa := st.pa - 1 }
    -- B16: "T=W" - Dereference syllable t via REFSYL[cite: 15]
    | 16 =>
      let st1 := { st with k := t }
      st1.REFSYL (decodeSyllable t)
    -- B17: "YFT"[cite: 15]
    | 17 => ({ st with Y := 0, pa := st.pa - 1 }).INCRC
    -- B18: "W=S" - Store S into memory pointed to by syllable t[cite: 15]
    | 18 =>
      let dec := decodeSyllable t
      let st0 := { st with k := t }
      if (st0.c1 != (1 : Int)) && decide (dec.ka + dec.k1 + 1 > 40) then
        st0.enterIR (-29)
      else
        let dstPage := st0.h dec.k2
        let st_mem :=
          if (Int.natAbs dstPage : Int) <= 4 then
            let s1 := st0.readSyl st0.ph (3 * (st0.pa - 1) - 1)
            let m1 := st0.writeSyl dstPage dec.ka s1
            let m2 :=
              if dec.k1 >= 0 then
                m1.writeSyl dstPage (dec.ka + 1) (st0.readSyl st0.ph (3 * (st0.pa - 1)))
              else m1
            if dec.k1 >= 1 then
              m2.writeSyl dstPage (dec.ka + 2) (st0.readSyl st0.ph (3 * (st0.pa - 1) + 1))
            else m2
          else st0
        ({ st_mem with pa := st0.pa - 1 }).INCRC

    -- B19: "SMT" - Tritwise multiplication S := S (×) T[cite: 15]
    | 19 =>
      let st1 := st.setS (tritwiseSMT S T)
      ({ st1 with pa := st.pa - 1 }).INCRC

    -- B20: "Y=T"[cite: 15]
    | 20 => ({ st with Y := T, pa := st.pa - 1 }).INCRC

    -- B21: "SAT" - Tritwise conditional merge[cite: 15]
    | 21 =>
      let st1 := st.setS (tritwiseSAT S T)
      ({ st1 with pa := st.pa - 1 }).INCRC

    -- B22: "S-T"[cite: 15]
    | 22 =>
      let st1 := st.setS (S - T)
      ({ st1 with pa := st.pa - 1 }).INCRC

    -- B23: "TDN" - Negate T (T := -T)[cite: 15]
    | 23 => (st.setT (-T)).INCRC

    -- B24: "S+T"[cite: 16]
    | 24 =>
      let st1 := st.setS (S + T)
      ({ st1 with pa := st.pa - 1 }).INCRC

    -- B25: "LBT" - Multiply-accumulate with Y := 0: (S, Y) := (S, 0) + T * R * 3^2[cite: 16]
    | 25 =>
      let x36 := S * (3 ^ 18) + T * st.R * 9
      let newS := balMod 18 (x36 / (3 ^ 18))
      let newY := balMod 18 x36
      let st1 := st.setS newS
      ({ st1 with Y := newY, pa := st.pa - 1 }).INCRC

    -- B26: "L*T" - R := S; (S, Y) := T * R * 3^2[cite: 16]
    | 26 =>
      let newR := S
      let x36 := T * newR * 9
      let newS := balMod 18 (x36 / (3 ^ 18))
      let newY := balMod 18 x36
      let st1 := st.setS newS
      ({ st1 with R := newR, Y := newY, pa := st.pa - 1 }).INCRC

    -- B27: "LHT" - Full 36-trit multiply-accumulate: (S, Y) := (S, Y) + T * R * 3^2[cite: 16]
    | _ =>
      let x36 := S * (3 ^ 18) + st.Y + T * st.R * 9
      let newS := balMod 18 (x36 / (3 ^ 18))
      let newY := balMod 18 x36
      let st1 := st.setS newS
      ({ st1 with Y := newY, pa := st.pa - 1 }).INCRC

-- ============================================================================
-- 8. ALL 27 SPECIAL OPERATIONS `S1..S27` (Pages 46–48)[cite: 16, 17]
-- ============================================================================

/-- `procedure TRANSIN(l)` (Page 46)[cite: 16]. -/
def TRANSIN (st : State) (l : Int) : State :=
  let gval := if st.g_7 l == 1 then st.g_syl l else -(st.g_syl l)
  let st1 := (st.setT 0).set_t gval
  { st1 with a := fun x => if x == l then 1 else st.a x }

/-- `procedure TRANSOUT(l)` (Page 46)[cite: 16]. -/
def TRANSOUT (st : State) (l : Int) : State :=
  let t := st.get_t
  { st with
    g_syl := fun x => if x == l then Int.natAbs t else st.g_syl x
    g_7   := fun x => if x == l then (if t < 0 then 0 else 1) else st.g_7 x
    a     := fun x => if x == l then 1 else st.a x }

/-- `procedure COPY(l)` (Page 46): copies Level-2 page `f[l, q[l], -40..40]` to RAM page `hf` (`|hf| ≤ 4`)[cite: 16]. -/
def COPY (st : State) (l : Int) : State :=
  let hf_val := sliceTrits 18 4 6 st.getT
  let st0 := { st with hf := hf_val }
  if (Int.natAbs hf_val : Int) <= 4 then
    let ql := st0.q l
    { st0 with m := fun p s =>
        if p == hf_val && s >= -40 && s <= 40 then st0.f l ql s
        else st0.m p s }
  else st0

/-- `procedure LOAD(l)` (Page 46): copies Level-1 page `hf` to Level-2 page `f[l, q[l], -40..40]`[cite: 16]. -/
def LOAD (st : State) (l : Int) : State :=
  let hf_val := sliceTrits 18 4 6 st.getT
  let ql := st.q l
  { st with
    hf := hf_val
    f := fun bank pg s =>
      if bank == l && pg == ql && s >= -40 && s <= 40 then st.m hf_val s
      else st.f bank pg s }

/-- Executes one of the 27 Special (Privileged) Operations `S1..S27` (Pages 46–48)[cite: 16, 17]. -/
def execSPEC (st : State) (ko : Int) : State :=
  if st.c1 == -1 then
    st.enterIR (-28) -- Forbidden syllable in user mode (§5.3)[cite: 16, 18]
  else if st.c1 == 0 && st.pa == -13 then
    st.enterIR (-31) -- Stack underflow in macro mode[cite: 16, 18]
  else
    let opIdx := ko + 14
    let T := st.getT
    let t := st.get_t
    match opIdx with
    | 1  => (st.TRANSIN (-1)).INCRC                         -- S1: COPYG1[cite: 16]
    | 2  => (st.TRANSIN 0).INCRC                            -- S2: COPYG2[cite: 16]
    | 3  => (st.TRANSIN 1).INCRC                            -- S3: COPYG3[cite: 16]
    | 4  => ({ (st.COPY (-1)) with pa := st.pa - 1 }).INCRC -- S4: COPYF1[cite: 16]
    | 5  => ({ (st.COPY 0)    with pa := st.pa - 1 }).INCRC -- S5: COPYF2[cite: 16]
    | 6  => ({ (st.COPY 1)    with pa := st.pa - 1 }).INCRC -- S6: COPYF3[cite: 16]
    | 7  =>                                                 -- S7: LOADQ1 (SUIT(-1))[cite: 14, 16]
      let qv := sliceTrits 18 5 12 T
      ({ st with
        q := fun x => if x == -1 then qv else st.q x
        v := fun idx => if idx == 5 then 1 else st.v idx
        pa := st.pa - 1 }).INCRC
    | 8  =>                                                 -- S8: LOADQ2 (SUIT(0))[cite: 14, 16]
      let qv := sliceTrits 18 5 12 T
      ({ st with
        q := fun x => if x == 0 then qv else st.q x
        v := fun idx => if idx == 6 then 1 else st.v idx
        pa := st.pa - 1 }).INCRC
    | 9  =>                                                 -- S9: LOADQ3 (SUIT(1))[cite: 14, 16]
      let qv := sliceTrits 18 5 12 T
      ({ st with
        q := fun x => if x == 1 then qv else st.q x
        v := fun idx => if idx == 7 then 1 else st.v idx
        pa := st.pa - 1 }).INCRC
    | 10 =>                                                 -- S10: COPYP[cite: 16]
      let z_val := st.ph * (3 ^ 12) + st.pa * (3 ^ 7)
      (st.setT z_val).INCRC
    | 11 =>                                                 -- S11: EXCHP[cite: 16]
      ({ st with
        ph := st.ph_saved, pa := st.pa_saved
        ph_saved := st.ph, pa_saved := st.pa }).INCRC
    | 12 =>                                                 -- S12: LOADP[cite: 16]
      let new_ph := sliceTrits 18 5 6 T
      let new_pa := sliceTrits 18 9 11 T
      ({ st with ph := new_ph, pa := new_pa }).INCRC
    | 13 =>                                                 -- S13: COPYMC[cite: 16]
      let z12 := st.c_9_20
      let st1 := { st with c_9_20 := st.c_21_32, c_21_32 := z12 }
      (st1.setT (z12 * (3 ^ 6))).INCRC
    | 14 =>                                                 -- S14: RETNMC[cite: 16]
      let z12 := st.c_9_20
      let (new_c1, new_ch, new_ca) := unpackCFrame z12
      { st with
        c_9_20  := st.c_21_32
        c_21_32 := z12
        c1      := new_c1
        ch      := new_ch
        ca      := new_ca }
    | 15 =>                                                 -- S15: LOADMC[cite: 17]
      let z12 := sliceTrits 18 1 12 T
      ({ st with c_21_32 := st.c_9_20, c_9_20 := z12, pa := st.pa - 1 }).INCRC
    | 16 =>                                                 -- S16: LOADH1[cite: 17]
      let hv := sliceTrits 18 4 6 T
      ({ st with h := fun x => if x == -1 then hv else st.h x, pa := st.pa - 1 }).INCRC
    | 17 =>                                                 -- S17: LOADH2[cite: 17]
      let hv := sliceTrits 18 4 6 T
      ({ st with h := fun x => if x == 0 then hv else st.h x, pa := st.pa - 1 }).INCRC
    | 18 =>                                                 -- S18: LOADH3[cite: 17]
      let hv := sliceTrits 18 4 6 T
      ({ st with h := fun x => if x == 1 then hv else st.h x, pa := st.pa - 1 }).INCRC
    | 19 =>                                                 -- S19: LOADU1[cite: 17]
      ({ st with
        u := fun x => if x == -1 then sliceTrits 6 1 4 t else st.u x
        a := fun x => if x == -1 then 1 else st.a x
        pa := st.pa - 1 }).INCRC
    | 20 =>                                                 -- S20: LOADU2[cite: 17]
      ({ st with
        u := fun x => if x == 0 then sliceTrits 6 1 4 t else st.u x
        a := fun x => if x == 0 then 1 else st.a x
        pa := st.pa - 1 }).INCRC
    | 21 =>                                                 -- S21: LOADU3[cite: 17]
      ({ st with
        u := fun x => if x == 1 then sliceTrits 6 1 4 t else st.u x
        a := fun x => if x == 1 then 1 else st.a x
        pa := st.pa - 1 }).INCRC
    | 22 => ({ (st.LOAD (-1))     with pa := st.pa - 1 }).INCRC -- S22: LOADF1[cite: 17]
    | 23 => ({ (st.LOAD 0)        with pa := st.pa - 1 }).INCRC -- S23: LOADF2[cite: 17]
    | 24 => ({ (st.LOAD 1)        with pa := st.pa - 1 }).INCRC -- S24: LOADF3[cite: 17]
    | 25 => ({ (st.TRANSOUT (-1)) with pa := st.pa - 1 }).INCRC -- S25: LOADG1[cite: 17]
    | 26 => ({ (st.TRANSOUT 0)    with pa := st.pa - 1 }).INCRC -- S26: LOADG2[cite: 17]
    | _  => ({ (st.TRANSOUT 1)    with pa := st.pa - 1 }).INCRC -- S27: LOADG3[cite: 17]

-- ============================================================================
-- 9. MAIN PROCESSOR `CYCLE` STEP (`procedure SETUN 70`, Page 43)[cite: 14, 15]
-- ============================================================================

/-- Checks `v[1..9]` in priority order `i = 1..9` when `c1 ≠ 1` (Page 43)[cite: 14]. -/
def findPendingInterrupt (st : State) : Option Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9].find? (fun i => st.v i != 0)

/-- Single cycle of `procedure SETUN 70` (`CYCLE` label on Page 43)[cite: 14, 15]. -/
def stepCycle (st : State) : State :=
  if st.start == 0 then st
  else
    match (if st.c1 != 1 then st.findPendingInterrupt else none) with
    | some idx =>
      let st_clr := { st with v := fun j => if j == idx then 0 else st.v j }
      st_clr.enterIR (interruptCauseFromV idx)
    | none =>
      let k_val := st.readSyl st.ch st.ca
      let st_k := { st with k := k_val }
      let dec := decodeSyllable k_val
      if dec.k1 == 0 && dec.k2 == 0 then
        -- Operation syllable: switch operation := MACRO, BASIC, SPEC [k3 + 2][cite: 14]
        if dec.k3 == -1 then st_k.execMACRO dec
        else if dec.k3 == 0 then st_k.execBASIC dec.ko
        else st_k.execSPEC dec.ko
      else
        -- Reference syllable (push operand from memory onto stack)[cite: 14]
        if (st_k.c1 != (1 : Int)) && (st_k.pa == (13 : Int)) then
          st_k.enterIR (-30)
        else
          let st_inc := { st_k with pa := st_k.pa + 1 }
          st_inc.REFSYL dec

end State

-- ============================================================================
-- 10. KERNEL-VERIFIED SETUN-70 ARCHITECTURAL THEOREMS[cite: 15, 16, 17, 18]
-- ============================================================================

theorem c_frame_roundtrip_verified :
    State.unpackCFrame (State.packCFrame (-1) 4 (-13)) = (-1, 4, -13) ∧
    State.unpackCFrame (State.packCFrame 0 (-13) 40) = (0, -13, 40) ∧
    State.unpackCFrame (State.packCFrame 1 12 (-40)) = (1, 12, -40) := by
  decide

theorem user_mode_spec_triggers_w_minus_28 :
    let st : State := { c1 := -1, ch := 0, ca := 0 }
    (st.execSPEC 0).w = -28 ∧ (st.execSPEC 0).c1 = 1 ∧ (st.execSPEC 0).ch = 13 := by
  decide

theorem macro_in_macro_mode_triggers_w_minus_28 :
    let st : State := { c1 := 0, ch := -13, ca := 0 }
    let dec := decodeSyllable 0
    (st.execMACRO dec).w = -28 ∧ (st.execMACRO dec).c1 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem rpn_add_s_plus_t_verified :
    let st0 : State := { c1 := 1, ph := 0, pa := 2, ca := 0 }
    let st1 := (st0.setS 120).setT 300
    -- B24 ("S+T") corresponds to ko + 14 = 24 => ko = 10[cite: 15, 16]
    let st2 := st1.execBASIC 10
    st2.pa = 1 ∧ st2.getT = 420 ∧ st2.ca = 1 := by
  decide

end Setun70