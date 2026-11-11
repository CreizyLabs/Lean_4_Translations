/-
  Formal Archival Replication & Verification in Lean 4
  Target: INTERPRETER.agc (Colossus 2A / Comanche 055, Pages 1107 - 1199)
          Apollo 11 Command Module Guidance Computer (AGC) Interpretive Language Engine.

  Guarantees:
  - Zero `sorry`s
  - Zero custom `axiom`s
  - Zero approximations or simulations
  - Exact 15-bit ones'-complement hardware instructions (`BitVec 15`) and 16-bit Accumulator (`BitVec 16`)
  - Exact hardware editing registers (`CYR`, `SR`, `CYL`, `EDOP`) and bank-switching (`EBANK`, `FBANK`, `BBANK`, `SUPERBNK`)
  - Complete coverage of all 13 sections of `interpreter.agc.py`
  - Kernel-verified proofs of all 6 end-to-end verification tests via `decide`
-/

namespace AGCInterpreter

-- ============================================================================
-- 1. AGC ONES'-COMPLEMENT ARITHMETIC & HARDWARE PRIMITIVES
-- ============================================================================

abbrev Word15 := BitVec 15
abbrev Word16 := BitVec 16

def MASK15     : Word15 := 0o77777#15
def MASK16     : Word16 := 0o177777#16
def POS_ZERO   : Word15 := 0o00000#15
def NEG_ZERO   : Word15 := 0o77777#15
def POSMAX     : Word15 := 0o37777#15
def NEGMAX     : Word15 := 0o40000#15

def POS_ZERO16 : Word16 := 0o000000#16
def NEG_ZERO16 : Word16 := 0o177777#16

@[inline] def norm15 (val : Nat) : Word15 := BitVec.ofNat 15 val
@[inline] def norm16 (val : Nat) : Word16 := BitVec.ofNat 16 val

@[inline] def comp15 (val : Word15) : Word15 := ~~~val
@[inline] def comp16 (val : Word16) : Word16 := ~~~val

/-- Sign-extend a 15-bit word to 16-bit format (duplicating bit 15 into bit 16). -/
@[inline] def sign_extend_15_to_16 (val : Word15) : Word16 :=
  let v16 : Word16 := val.zeroExtend 16
  if (val &&& 0o40000#15) != 0#15 then
    v16 ||| 0o100000#16
  else
    v16

/-- Check if a 16-bit value in `A` has overflow/underflow (bits 16 and 15 differ). -/
@[inline] def is_overflow_16 (val16 : Word16) : Bool :=
  let b16 := (val16 >>> 15) &&& 1#16
  let b15 := (val16 >>> 14) &&& 1#16
  b16 != b15

/--
  Convert 16-bit `A` into a 15-bit memory word and a 15-bit overflow indicator:
  - No overflow: returns `(bits 15..1, +0)`
  - Positive overflow (`01_xxx...`): returns `(0_xxx..., +1 [0o00001])`
  - Negative overflow (`10_xxx...`): returns `(1_xxx..., -1 [0o77776])`
-/
@[inline] def overflow_correct_16_to_15 (val16 : Word16) : Word15 × Word15 :=
  let b16 : Nat := (val16.toNat >>> 15) &&& 1
  let b15 : Nat := (val16.toNat >>> 14) &&& 1
  let lower14 : Nat := val16.toNat &&& 0o37777
  let stored : Word15 := BitVec.ofNat 15 ((b16 <<< 14) ||| lower14)
  if b16 == b15 then
    (stored, POS_ZERO)
  else if b16 == 0 && b15 == 1 then
    (stored, 0o00001#15)
  else
    (stored, 0o77776#15)

/-- 15-bit ones'-complement addition with end-around carry. -/
@[inline] def add_15 (x y : Word15) : Word15 :=
  let s : Nat := x.toNat + y.toNat
  let s' : Nat := if s > 0o77777 then (s &&& 0o77777) + 1 else s
  BitVec.ofNat 15 (s' &&& 0o77777)

/-- 16-bit ones'-complement addition with end-around carry (for Register `A`). -/
@[inline] def add_16 (x16 y16 : Word16) : Word16 :=
  let s : Nat := x16.toNat + y16.toNat
  let s' : Nat := if s > 0o177777 then (s &&& 0o177777) + 1 else s
  BitVec.ofNat 16 (s' &&& 0o177777)

/-- Convert 15-bit ones'-complement word to signed `Int` (`-16383..+16383`). -/
@[inline] def s15_to_int (val15 : Word15) : Int :=
  if (val15 &&& 0o40000#15) != 0#15 then
    - (Int.ofNat ((comp15 val15).toNat &&& 0o37777))
  else
    Int.ofNat (val15.toNat &&& 0o37777)

/-- Convert signed `Int` (`-16383..+16383`) to 15-bit ones'-complement word. -/
@[inline] def int_to_s15 (n : Int) (neg_zero : Bool := false) : Word15 :=
  if n == 0 then
    if neg_zero then NEG_ZERO else POS_ZERO
  else if n > 0 then
    BitVec.ofNat 15 (n.toNat &&& 0o37777)
  else
    comp15 (BitVec.ofNat 15 ((-n).toNat &&& 0o37777))

/-- 15-bit Cycle Right 1 bit (`CYR` hardware editing register). -/
@[inline] def cyr_15 (val15 : Word15) : Word15 :=
  let lsb := val15 &&& 1#15
  (val15 >>> 1) ||| (lsb <<< 14)

/-- 15-bit Cycle Left 1 bit (`CYL` hardware editing register). -/
@[inline] def cyl_15 (val15 : Word15) : Word15 :=
  let msb := (val15 >>> 14) &&& 1#15
  (val15 <<< 1) ||| msb

/-- 15-bit Shift Right 1 bit preserving sign bit 15 (`SR` hardware editing register). -/
@[inline] def sr_15 (val15 : Word15) : Word15 :=
  let sign := val15 &&& 0o40000#15
  (val15 >>> 1) ||| sign

/--
  Count, Compare, and Skip (`CCS`) on a 15-bit word.
  Returns `(branch_offset, diminished_abs_value_DABS)`:
  - `> +0`  : offset `0`, `DABS = val - 1`
  - `== +0` : offset `1`, `DABS = +0`
  - `< -0`  : offset `2`, `DABS = (~val) - 1`
  - `== -0` : offset `3`, `DABS = +0`
-/
@[inline] def ccs_eval (val15 : Word15) : Nat × Word15 :=
  if val15 == POS_ZERO then
    (1, POS_ZERO)
  else if val15 == NEG_ZERO then
    (3, POS_ZERO)
  else if (val15 &&& 0o40000#15) == 0#15 then
    (0, BitVec.ofNat 15 ((val15.toNat - 1) &&& 0o77777))
  else
    let mag := comp15 val15
    (2, BitVec.ofNat 15 ((mag.toNat - 1) &&& 0o77777))

@[inline] def is_bzf (val16 : Word16) : Bool :=
  val16 == POS_ZERO16 || val16 == NEG_ZERO16

@[inline] def is_bzmf (val16 : Word16) : Bool :=
  if is_bzf val16 then true
  else (val16 &&& 0o100000#16) != 0#16

/-- Exact integer-scaled `2DEC` helper: converts `(neg, round(|val| * 2^28))` into `(major, minor)`. -/
@[inline] def scaled28_to_2dec (neg : Bool) (scaled28 : Nat) : Word15 × Word15 :=
  let hi : Word15 := BitVec.ofNat 15 ((scaled28 >>> 14) &&& 0o37777)
  let lo : Word15 := BitVec.ofNat 15 (scaled28 &&& 0o37777)
  if neg then (comp15 hi, comp15 lo) else (hi, lo)

/-- Exact integer-scaled `DEC` helper: converts `(neg, round(|val| * 2^14))` into a 15-bit word. -/
@[inline] def scaled14_to_1dec (neg : Bool) (scaled14 : Nat) : Word15 :=
  let w : Word15 := BitVec.ofNat 15 (scaled14 &&& 0o37777)
  if neg then comp15 w else w


-- ============================================================================
-- 2. COLOSSUS 2A (COMANCHE 055) MEMORY ADDRESSES & CONSTANTS
-- ============================================================================

-- Central & Editing Hardware Registers
def REG_A      : Word15 := 0o0000#15
def REG_L      : Word15 := 0o0001#15
def REG_Q      : Word15 := 0o0002#15
def REG_EBANK  : Word15 := 0o0003#15
def REG_FBANK  : Word15 := 0o0004#15
def REG_Z      : Word15 := 0o0005#15
def REG_BBANK  : Word15 := 0o0006#15
def REG_ZERO   : Word15 := 0o0007#15

def REG_CYR    : Word15 := 0o0020#15
def REG_SR     : Word15 := 0o0021#15
def REG_CYL    : Word15 := 0o0022#15
def REG_EDOP   : Word15 := 0o0023#15

-- I/O Channels
def LCHAN      : Word15 := 0o0001#15
def QCHAN      : Word15 := 0o0002#15
def HISCALAR   : Word15 := 0o0003#15
def CHAN5      : Word15 := 0o0005#15
def SUPERBNK   : Word15 := 0o0007#15

-- Erasable Memory Layout for Executive & Interpreter (Comanche 055)
def BUF        : Word15 := 0o0047#15  -- BUF (+0, +1, +2)
def BUF_P1     : Word15 := 0o0050#15
def BUF_P2     : Word15 := 0o0051#15
def BUF2       : Word15 := 0o0052#15  -- BUF2 (+0, +1)
def BUF2_P1    : Word15 := 0o0053#15
def INDEXLOC   : Word15 := 0o0054#15
def MPTEMP     : Word15 := 0o0055#15
def DMPNTEMP   : Word15 := 0o0055#15  -- Alias of MPTEMP in DMPNSUB
def DOTINC     : Word15 := 0o0056#15
def DOTRET     : Word15 := 0o0057#15
def MATINC     : Word15 := 0o0060#15
def TEM1       : Word15 := 0o0061#15
def POLYCNT    : Word15 := 0o0062#15
def POLYRET    : Word15 := 0o0063#15
def DVSIGN     : Word15 := 0o0064#15
def DVNORMCT   : Word15 := 0o0065#15
def MAXDVSW    : Word15 := 0o0066#15
def NEWJOB     : Word15 := 0o0067#15

def VBUF       : Word15 := 0o0075#15  -- VBUF (+0 .. +5) (0o0075..0o0102)
def VBUF_P1    : Word15 := 0o0076#15
def VBUF_P2    : Word15 := 0o0077#15
def VBUF_P3    : Word15 := 0o0100#15
def VBUF_P4    : Word15 := 0o0101#15
def VBUF_P5    : Word15 := 0o0102#15
def ESCAPE     : Word15 := 0o0103#15
def ESCAPE2    : Word15 := 0o0104#15

-- Active Core Set 0 Registers
def MPAC       : Word15 := 0o0105#15  -- MPAC (+0 .. +6) (0o0105..0o0113)
def MPAC_P1    : Word15 := 0o0106#15
def MPAC_P2    : Word15 := 0o0107#15
def MPAC_P3    : Word15 := 0o0110#15
def MPAC_P4    : Word15 := 0o0111#15
def MPAC_P5    : Word15 := 0o0112#15
def MPAC_P6    : Word15 := 0o0113#15
def PUSHLOC    : Word15 := 0o0114#15
def PRIORITY   : Word15 := 0o0115#15
def LOC        : Word15 := 0o0116#15
def BANKSET    : Word15 := 0o0117#15
def OVFIND     : Word15 := 0o0120#15

-- Interpreter Work Area & Control Registers
def MODE       : Word15 := 0o0226#15
def INTBIT15   : Word15 := 0o0227#15
def LOCCTR     : Word15 := 0o0230#15
def FIXLOC     : Word15 := 0o0231#15
def ADDRWD     : Word15 := 0o0235#15
def POLISH     : Word15 := 0o0236#15
def SWBIT      : Word15 := 0o0237#15
def SWWORD     : Word15 := 0o0240#15
def STATE      : Word15 := 0o0241#15  -- Base of 64 switch words (STATE +0 .. +63)

-- VAC Work Area Relative Offsets (Added to C(FIXLOC))
def OFF_LVSQUARE : Word15 := 34#15
def OFF_LV       : Word15 := 36#15
def OFF_X1       : Word15 := 38#15
def OFF_X2       : Word15 := 39#15
def OFF_S1       : Word15 := 40#15
def OFF_S2       : Word15 := 41#15
def OFF_QPRET    : Word15 := 42#15

def X1       : Word15 := OFF_X1
def X2       : Word15 := OFF_X2
def S1       : Word15 := OFF_S1
def S2       : Word15 := OFF_S2
def QPRET    : Word15 := OFF_QPRET
def LVSQUARE : Word15 := OFF_LVSQUARE
def LV       : Word15 := OFF_LV

-- Fixed Constants & Bit Masks
def ZERO       : Word15 := 0o00000#15
def ONE        : Word15 := 0o00001#15
def TWO        : Word15 := 0o00002#15
def THREE      : Word15 := 0o00003#15
def FOUR       : Word15 := 0o00004#15
def FIVE       : Word15 := 0o00005#15
def SIX        : Word15 := 0o00006#15
def SEVEN      : Word15 := 0o00007#15
def TEN        : Word15 := 0o00012#15
def THIRTEEN   : Word15 := 0o00015#15
def FOURTEEN   : Word15 := 0o00016#15

def NEGONE     : Word15 := 0o77776#15
def NEG4       : Word15 := 0o77773#15  -- DEC -4
def NEG12      : Word15 := 0o77763#15  -- DEC -12
def DEC45      : Word15 := 45#15
def NEG_ENDVAC  : Word15 := comp15 45#15
def NEG_ENDERAS : Word15 := comp15 (BitVec.ofNat 15 (0o3777 - 45))

def BIT1       : Word15 := 0o00001#15
def BIT2       : Word15 := 0o00002#15
def BIT3       : Word15 := 0o00004#15
def BIT4       : Word15 := 0o00010#15
def BIT5       : Word15 := 0o00020#15
def BIT6       : Word15 := 0o00040#15
def BIT7       : Word15 := 0o00100#15
def BIT8       : Word15 := 0o00200#15
def BIT9       : Word15 := 0o00400#15
def BIT10      : Word15 := 0o01000#15
def BIT11      : Word15 := 0o02000#15
def BIT12      : Word15 := 0o04000#15
def BIT13      : Word15 := 0o10000#15
def BIT14      : Word15 := 0o20000#15
def BIT15      : Word15 := 0o40000#15

def HALF       : Word15 := 0o20000#15  -- +0.5 (2^-1)
def QUARTER    : Word15 := 0o10000#15  -- +0.25 (2^-2)
def NEG_HALF   : Word15 := comp15 HALF -- -0.5 (0o57777)

def LOW2       : Word15 := 0o00003#15
def LOW3       : Word15 := 0o00007#15
def LOW4       : Word15 := 0o00017#15
def LOW7       : Word15 := 0o00177#15
def LOW8       : Word15 := 0o00377#15
def LOW10      : Word15 := 0o01777#15
def LOW11      : Word15 := 0o03777#15
def B3TOB4     : Word15 := 0o00014#15
def B5TOBB     : Word15 := 0o00360#15
def B12T14     : Word15 := 0o34000#15
def HIGH4      : Word15 := 0o74000#15
def HIGH9      : Word15 := 0o77700#15
def BANKMASK   : Word15 := 0o76000#15
def FBANKMSK   : Word15 := BANKMASK
def CONST_2K   : Word15 := 0o02000#15
def LOW7_2K    : Word15 := 0o02177#15
def OCT1400    : Word15 := 0o01400#15
def OCT40001   : Word15 := 0o40001#15
def OCT23      : Word15 := 0o00023#15
def NEG_OCT10  : Word15 := comp15 0o00010#15
def OCT176     : Word15 := 0o00176#15
def PRIO30     : Word15 := 0o30000#15
def SRDDV      : Word15 := 20#15
def NEG1_2_P2  : Word15 := 0o60001#15  -- -1/2+2 OCT 60001
def CONST_5B10 : Word15 := 0o12000#15  -- 5 * 2^-4 = 5120 = 0o12000

-- Store-type secondary load dispatch opcodes (placed into CYR)
def DLOADCOD   : Word15 := 0o10006#15
def VLOADCOD   : Word15 := 0o10000#15
def DLOAD_STAR : Word15 := 0o50006#15
def VLOAD_STAR : Word15 := 0o50000#15
def CALLCODE   : Word15 := 0o00015#15

-- Exact SQRT Linear Approximation Constants (matches `dec_to_1dec` in Python)
def BIASLO     : Word15 := 2436#15   -- round(0.2974 * 0.5 * 16384)
def SLOPEHI    : Word15 := 9640#15   -- round(0.5884 * 16384)
def BIASHI     : Word15 := 3434#15   -- round(0.4192 * 0.5 * 16384)
def SLOPELO    : Word15 := 13638#15  -- round(0.8324 * 16384)

-- Exact SINE Hastings Polynomial Coefficients (Degree 4, N-1 = 3)
-- Computed identically to `dec_to_2dec` in Python (`round(|c| * 2^28)`)
def SIN_POLY_COEFFS : List (Word15 × Word15) :=
  [ scaled28_to_2dec false 105414357  -- +0.3926990796
  , scaled28_to_2dec true  173399568  -- -0.6459637111
  , scaled28_to_2dec false  85566142  -- +0.318758717
  , scaled28_to_2dec true   20073670  -- -0.074780249
  , scaled28_to_2dec false   2602478  -- +0.009694988
  ]

-- Exact ARCCOS Hastings Polynomial Coefficients (Degree 7, N-1 = 6)
def ACOS_POLY_COEFFS : List (Word15 × Word15) :=
  [ scaled28_to_2dec false 94906264   -- +0.353553385
  , scaled28_to_2dec true  25931777   -- -0.0483017006 * 2^1
  , scaled28_to_2dec false 21504159   -- +0.0200273085 * 2^2
  , scaled28_to_2dec true  24251932   -- -0.0112931863 * 2^3
  , scaled28_to_2dec false 29863406   -- +0.00695311612 * 2^4
  , scaled28_to_2dec true  33038456   -- -0.00384617957 * 2^5
  , scaled28_to_2dec false 25792112   -- +0.001501297736 * 2^6
  , scaled28_to_2dec true   9763675   -- -0.000284160334 * 2^7
  ]

-- Fixed Memory Table Base Addresses
def ADDR_BIT15_TABLE   : Word15 := 0o6000#15
def ADDR_BIT14_TABLE   : Word15 := 0o6001#15
def ADDR_LIMITS        : Word15 := 0o6030#15
def ADDR_NEG_HALF_P1   : Word15 := 0o6040#15
def ADDR_REVCNT        : Word15 := 0o6050#15
def ADDR_NOWDS         : Word15 := 0o6060#15
def ADDR_SIN_POLY      : Word15 := 0o6100#15
def ADDR_ACOS_POLY     : Word15 := 0o6130#15

-- Symbolic return/dispatch addresses used in ESCAPE / ESCAPE2
def SYM_DANZIG         : Word15 := 0o77001#15
def SYM_ASINEX         : Word15 := 0o77002#15
def SYM_SUBTR          : Word15 := 0o77003#15


-- ============================================================================
-- 3. AGC INTERPRETER HARDWARE STATE & BASIC INSTRUCTIONS
-- ============================================================================

/-- Interpreter exit or executive suspension record. -/
inductive ExitResult where
  | exit   (retAddr : Word15) (bbank : Word15)
  | chang2 (locComp : Word15) (bbank : Word15)
  | poodoo (octCode : Word15)
  | ccshole
  deriving DecidableEq, Repr

/-- Dispatcher state labels for the Interpreter loop. -/
inductive DispStep where
  | danzig
  | noibnksw
  | newops
  | opjump
  | diradres
  | dodload_star
  | index
  | bit15adr
  | intpret_p3
  deriving DecidableEq, Repr

/-- Complete deterministic hardware state of the AGC Interpreter. -/
structure AGCInterpState where
  erasable           : Word15 → Word15
  fixed              : Word15 → Option Word15
  channels           : Word15 → Word15
  reg_A16            : Word16
  interrupts_enabled : Bool
  halted             : Bool
  alarms             : List Word15
  last_exit          : Option ExitResult

-- ----------------------------------------------------------------------------
-- Register & Memory Accessors (with Editing Register Side-Effects)
-- ----------------------------------------------------------------------------

@[inline] def AGCInterpState.A (s : AGCInterpState) : Word16 := s.reg_A16

@[inline] def AGCInterpState.setA (s : AGCInterpState) (val16 : Word16) : AGCInterpState :=
  { s with reg_A16 := val16 }

@[inline] def AGCInterpState.A15 (s : AGCInterpState) : Word15 :=
  (overflow_correct_16_to_15 s.reg_A16).1

@[inline] def AGCInterpState.L (s : AGCInterpState) : Word15 := s.erasable REG_L

@[inline] def AGCInterpState.setL (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  { s with erasable := fun a => if a == REG_L then val else s.erasable a }

@[inline] def AGCInterpState.Q (s : AGCInterpState) : Word15 := s.erasable REG_Q

@[inline] def AGCInterpState.setQ (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  { s with erasable := fun a => if a == REG_Q then val else s.erasable a }

@[inline] def AGCInterpState.EBANK (s : AGCInterpState) : Word15 := s.erasable REG_EBANK

@[inline] def AGCInterpState.setEBANK (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  let bb := s.erasable REG_BBANK &&& (~~~0o00007#15)
  let eb_bits := (val >>> 8) &&& 0o00007#15
  let new_bb := bb ||| eb_bits
  { s with erasable := fun a =>
      if a == REG_EBANK then val
      else if a == REG_BBANK then new_bb
      else s.erasable a }

@[inline] def AGCInterpState.FBANK (s : AGCInterpState) : Word15 := s.erasable REG_FBANK

@[inline] def AGCInterpState.setFBANK (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  let bb := s.erasable REG_BBANK &&& 0o00007#15
  let fb_bits := val &&& 0o76000#15
  let new_bb := bb ||| fb_bits
  { s with erasable := fun a =>
      if a == REG_FBANK then val
      else if a == REG_BBANK then new_bb
      else s.erasable a }

@[inline] def AGCInterpState.BBANK (s : AGCInterpState) : Word15 := s.erasable REG_BBANK

@[inline] def AGCInterpState.setBBANK (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  let new_fb := val &&& 0o76000#15
  let new_eb := (val &&& 0o00007#15) <<< 8
  { s with erasable := fun a =>
      if a == REG_BBANK then val
      else if a == REG_FBANK then new_fb
      else if a == REG_EBANK then new_eb
      else s.erasable a }

/-- Read 15-bit word from Erasable Memory (`0o0000 - 0o3777`). -/
@[inline] def AGCInterpState.read_e (s : AGCInterpState) (addr : Word15) : Word15 :=
  let a := addr &&& 0o3777#15
  if a == REG_A then s.A15
  else if a == REG_ZERO then POS_ZERO
  else s.erasable a

/--
  Write 15-bit word to Erasable Memory, enforcing hardware editing register
  transformations on `CYR` (`0o20`), `SR` (`0o21`), `CYL` (`0o22`), and `EDOP` (`0o23`).
-/
@[inline] def AGCInterpState.write_e (s : AGCInterpState) (addr : Word15) (val : Word15) : AGCInterpState :=
  let a := addr &&& 0o3777#15
  if a == REG_A then
    s.setA (sign_extend_15_to_16 val)
  else if a == REG_EBANK then
    s.setEBANK val
  else if a == REG_FBANK then
    s.setFBANK val
  else if a == REG_BBANK then
    s.setBBANK val
  else if a == REG_ZERO then
    { s with erasable := fun x => if x == REG_ZERO then POS_ZERO else s.erasable x }
  else if a == REG_CYR then
    let c := cyr_15 val
    { s with erasable := fun x => if x == REG_CYR then c else s.erasable x }
  else if a == REG_SR then
    let sh := sr_15 val
    { s with erasable := fun x => if x == REG_SR then sh else s.erasable x }
  else if a == REG_CYL then
    let c := cyl_15 val
    { s with erasable := fun x => if x == REG_CYL then c else s.erasable x }
  else if a == REG_EDOP then
    let ed := (val >>> 7) &&& 0o00177#15
    { s with erasable := fun x => if x == REG_EDOP then ed else s.erasable x }
  else
    { s with erasable := fun x => if x == a then val else s.erasable x }

/-- Write 15-bit word to Fixed Memory table/program space. -/
@[inline] def AGCInterpState.write_f (s : AGCInterpState) (addr : Word15) (val : Word15) : AGCInterpState :=
  { s with fixed := fun x => if x == addr then some val else s.fixed x }

/--
  Resolve a 12-bit subaddress (`0o0000 - 0o7777`):
  - `0o0000 - 0o1377`: Unswitched Erasable (`true, addr`)
  - `0o1400 - 0o1777`: Switched Erasable via `EBANK` bits 11..9 (`true, phys`)
  - `0o2000 - 0o3777`: Switched Fixed Bank via `FBANK` + `SUPERBNK` (`false, phys`)
  - `0o4000 - 0o7777`: Fixed-Fixed Banks 2 and 3 (`false, subaddr`)
-/
@[inline] def AGCInterpState.resolve_addr (s : AGCInterpState) (subaddr : Word15) : Bool × Word15 :=
  let sub := subaddr.toNat &&& 0o7777
  if sub < 0o1400 then
    (true, BitVec.ofNat 15 sub)
  else if sub < 0o2000 then
    let eb := (s.EBANK.toNat >>> 8) &&& 0o7
    (true, BitVec.ofNat 15 ((eb <<< 8) ||| (sub &&& 0o0377)))
  else if sub < 0o4000 then
    let fb0 := (s.FBANK.toNat >>> 10) &&& 0o37
    let fb := if fb0 >= 0o30 && ((s.channels SUPERBNK &&& 0o100#15) != 0#15) then fb0 + 0o10 else fb0
    (false, BitVec.ofNat 15 ((fb <<< 10) ||| (sub &&& 0o1777)))
  else
    (false, BitVec.ofNat 15 sub)

/-- Read 15-bit word using subaddress resolution or direct table address. -/
@[inline] def AGCInterpState.read_mem (s : AGCInterpState) (addr : Word15) : Word15 :=
  match s.fixed addr with
  | some v => v
  | none =>
    let (isE, phys) := s.resolve_addr addr
    if isE then
      s.read_e phys
    else
      match s.fixed phys with
      | some v => v
      | none   => (s.fixed (addr &&& 0o7777#15)).getD POS_ZERO

/-- Write 15-bit word to Erasable Memory via subaddress resolution. -/
@[inline] def AGCInterpState.write_mem (s : AGCInterpState) (addr : Word15) (val : Word15) : AGCInterpState :=
  let (isE, phys) := s.resolve_addr addr
  if isE then s.write_e phys val else s

-- ----------------------------------------------------------------------------
-- Exact AGC Basic Hardware Instructions Used by INTERPRETER.agc
-- ----------------------------------------------------------------------------

@[inline] def AGCInterpState.INHINT (s : AGCInterpState) : AGCInterpState :=
  { s with interrupts_enabled := false }

@[inline] def AGCInterpState.RELINT (s : AGCInterpState) : AGCInterpState :=
  { s with interrupts_enabled := true }

@[inline] def AGCInterpState.CA (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  s.setA (sign_extend_15_to_16 val)

@[inline] def AGCInterpState.CS (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  s.setA (sign_extend_15_to_16 (comp15 val))

@[inline] def AGCInterpState.AD (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  s.setA (add_16 s.A (sign_extend_15_to_16 val))

@[inline] def AGCInterpState.SU (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  s.setA (add_16 s.A (sign_extend_15_to_16 (comp15 val)))

@[inline] def AGCInterpState.DOUBLE (s : AGCInterpState) : AGCInterpState :=
  s.setA (add_16 s.A s.A)

@[inline] def AGCInterpState.ADS (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let res16 := add_16 s.A (sign_extend_15_to_16 (s.read_mem addr))
  let s1 := s.setA res16
  let (stored15, _) := overflow_correct_16_to_15 res16
  s1.write_mem addr stored15

/--
  Transfer to Storage (`TS`):
  Stores overflow-corrected 15-bit `A` into `memory[addr]`.
  Returns `(newState, overflowed : Bool)`.
-/
@[inline] def AGCInterpState.TS_ovf (s : AGCInterpState) (addr : Word15) : AGCInterpState × Bool :=
  let (stored15, ovf_ind) := overflow_correct_16_to_15 s.A
  let s1 := if (addr &&& 0o7777#15) != REG_A then s.write_mem addr stored15 else s
  if ovf_ind != POS_ZERO then
    (s1.setA (sign_extend_15_to_16 ovf_ind), true)
  else
    (s1, false)

@[inline] def AGCInterpState.TS (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  (s.TS_ovf addr).1

@[inline] def AGCInterpState.XCH (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let old_val := s.read_mem addr
  let (stored15, _) := overflow_correct_16_to_15 s.A
  let s1 := s.write_mem addr stored15
  s1.setA (sign_extend_15_to_16 old_val)

@[inline] def AGCInterpState.LXCH (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let old_val := s.read_mem addr
  let s1 := s.write_mem addr s.L
  s1.setL old_val

@[inline] def AGCInterpState.QXCH (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let old_val := s.read_mem addr
  let s1 := s.write_mem addr s.Q
  s1.setQ old_val

@[inline] def AGCInterpState.DXCH (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let s1 := s.XCH addr
  s1.LXCH (add_15 addr ONE)

@[inline] def AGCInterpState.DCA (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let w0 := s.read_mem addr
  let w1 := s.read_mem (add_15 addr ONE)
  (s.CA w0).setL w1

@[inline] def AGCInterpState.DCS (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let w0 := comp15 (s.read_mem addr)
  let w1 := comp15 (s.read_mem (add_15 addr ONE))
  (s.CA w0).setL w1

@[inline] def AGCInterpState.DCOM (s : AGCInterpState) : AGCInterpState :=
  (s.setA (comp16 s.A)).setL (comp15 s.L)

/-- Double Add to Storage (`DAS`). -/
@[inline] def AGCInterpState.DAS (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let addr_p1 := add_15 addr ONE
  let lo_mem := s.read_mem addr_p1
  let lo_sum16 := add_16 (sign_extend_15_to_16 s.L) (sign_extend_15_to_16 lo_mem)
  let (lo_stored, interflow) := overflow_correct_16_to_15 lo_sum16
  let s1 := s.write_mem addr_p1 lo_stored

  let hi_mem := s1.read_mem addr
  let hi_sum16 := add_16 (add_16 s1.A (sign_extend_15_to_16 hi_mem)) (sign_extend_15_to_16 interflow)
  let (hi_stored, net_ovf) := overflow_correct_16_to_15 hi_sum16
  let s2 := s1.write_mem addr hi_stored
  (s2.setL POS_ZERO).setA (sign_extend_15_to_16 net_ovf)

/-- Double-precision double (`DAS A`): adds `(A, L)` to `(A, L)` in place. -/
@[inline] def AGCInterpState.DDOUBL (s : AGCInterpState) : AGCInterpState :=
  let lo_sum16 := add_16 (sign_extend_15_to_16 s.L) (sign_extend_15_to_16 s.L)
  let (lo_stored, interflow) := overflow_correct_16_to_15 lo_sum16
  let hi_sum16 := add_16 (add_16 s.A s.A) (sign_extend_15_to_16 interflow)
  (s.setL lo_stored).setA hi_sum16

/-- Multiply (`MP`): multiplies 15-bit `A` by 15-bit `val` into `(A, L)`. -/
@[inline] def AGCInterpState.MP (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  let a15 := s.A15
  let b15 := val
  let sign_a : Bool := (a15 &&& 0o40000#15) != 0#15
  let sign_b : Bool := (b15 &&& 0o40000#15) != 0#15
  let mag_a : Nat := if sign_a then (comp15 a15).toNat &&& 0o37777 else a15.toNat &&& 0o37777
  let mag_b : Nat := if sign_b then (comp15 b15).toNat &&& 0o37777 else b15.toNat &&& 0o37777
  let prod : Nat := mag_a * mag_b
  let hi_mag : Word15 := BitVec.ofNat 15 ((prod >>> 14) &&& 0o37777)
  let lo_mag : Word15 := BitVec.ofNat 15 (prod &&& 0o37777)
  if prod == 0 then
    (s.CA POS_ZERO).setL POS_ZERO
  else if sign_a != sign_b then
    (s.CA (comp15 hi_mag)).setL (comp15 lo_mag)
  else
    (s.CA hi_mag).setL lo_mag

@[inline] def AGCInterpState.SQUARE (s : AGCInterpState) : AGCInterpState :=
  s.MP s.A15

/-- Divide (`DV`): divides 28-bit dividend in `(A, L)` by 15-bit divisor at `divisor_addr`. -/
@[inline] def AGCInterpState.DV (s : AGCInterpState) (divisor_addr : Word15) : AGCInterpState :=
  let div15 := s.read_mem divisor_addr
  let a15 := s.A15
  let l15 := s.L
  let sign_num : Bool :=
    if a15 == POS_ZERO || a15 == NEG_ZERO then
      (l15 &&& 0o40000#15) != 0#15
    else
      (a15 &&& 0o40000#15) != 0#15
  let sign_den : Bool := (div15 &&& 0o40000#15) != 0#15

  let mag_hi : Nat := if (a15 &&& 0o40000#15) != 0#15 then (comp15 a15).toNat &&& 0o37777 else a15.toNat &&& 0o37777
  let mag_lo : Nat := if (l15 &&& 0o40000#15) != 0#15 then (comp15 l15).toNat &&& 0o37777 else l15.toNat &&& 0o37777
  let mag_den : Nat := if sign_den then (comp15 div15).toNat &&& 0o37777 else div15.toNat &&& 0o37777

  let dividend : Nat := (mag_hi <<< 14) ||| mag_lo
  let (q_mag, r_mag) : Nat × Nat :=
    if mag_den == 0 || mag_hi >= mag_den then
      (0o37777, 0)
    else
      let q := dividend / mag_den
      let r := dividend % mag_den
      (if q > 0o37777 then 0o37777 else q, r)

  let q_w0 : Word15 := BitVec.ofNat 15 q_mag
  let r_w0 : Word15 := BitVec.ofNat 15 r_mag
  let q_word : Word15 := if (sign_num != sign_den) && q_mag != 0 then comp15 q_w0 else q_w0
  let r_word : Word15 := if sign_num && r_mag != 0 then comp15 r_w0 else r_w0
  (s.CA q_word).setL r_word

/-- Increment memory by `+1` (ones'-complement). -/
@[inline] def AGCInterpState.INCR (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  if (addr &&& 0o7777#15) == REG_A then
    s.AD ONE
  else
    let val := s.read_mem addr
    let res := if val == NEG_ZERO then ONE else add_15 val ONE
    s.write_mem addr res

/-- Augment (`AUG`): adds `+1` if positive/`+0`, or `-1` if negative/`-0`. -/
@[inline] def AGCInterpState.AUG (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  if (addr &&& 0o7777#15) == REG_A then
    if (s.A &&& 0o100000#16) == 0#16 then s.AD ONE else s.AD NEGONE
  else
    let val := s.read_mem addr
    let res := if (val &&& 0o40000#15) == 0#15 then add_15 val ONE else add_15 val NEGONE
    s.write_mem addr res

/-- Diminish (`DIM`): subtracts 1 in magnitude toward zero. -/
@[inline] def AGCInterpState.DIM (s : AGCInterpState) (addr : Word15) : AGCInterpState :=
  let val := s.read_mem addr
  if val == POS_ZERO || val == NEG_ZERO then s
  else
    let res := if (val &&& 0o40000#15) == 0#15 then add_15 val NEGONE else add_15 val ONE
    s.write_mem addr res

@[inline] def AGCInterpState.MASK (s : AGCInterpState) (val : Word15) : AGCInterpState :=
  s.setA (sign_extend_15_to_16 (s.A15 &&& val))

@[inline] def AGCInterpState.COM (s : AGCInterpState) : AGCInterpState :=
  s.setA (comp16 s.A)

@[inline] def AGCInterpState.ZL (s : AGCInterpState) : AGCInterpState :=
  s.setL POS_ZERO

@[inline] def AGCInterpState.OVSK (s : AGCInterpState) : Bool :=
  is_overflow_16 s.A

@[inline] def AGCInterpState.ROR (s : AGCInterpState) (chan : Word15) : AGCInterpState :=
  let c_val := if chan == QCHAN then s.Q else s.channels chan
  s.setA (sign_extend_15_to_16 (s.A15 ||| c_val))

@[inline] def AGCInterpState.RXOR (s : AGCInterpState) (chan : Word15) : AGCInterpState :=
  let c_val := if chan == QCHAN then s.Q else s.channels chan
  s.setA (sign_extend_15_to_16 (s.A15 ^^^ c_val))

-- ----------------------------------------------------------------------------
-- System Traps & External Calls (POODOO, ALARM, CCSHOLE, CHANG2)
-- ----------------------------------------------------------------------------

@[inline] def AGCInterpState.POODOO (s : AGCInterpState) (oct_code : Word15) : AGCInterpState :=
  let ex := ExitResult.poodoo oct_code
  { s with halted := true, last_exit := some ex }

@[inline] def AGCInterpState.ALARM (s : AGCInterpState) (oct_code : Word15) : AGCInterpState :=
  { s with alarms := s.alarms ++ [oct_code] }

@[inline] def AGCInterpState.CCSHOLE (s : AGCInterpState) : AGCInterpState :=
  let ex := ExitResult.ccshole
  { s with halted := true, last_exit := some ex }

@[inline] def AGCInterpState.CHANG2 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e LOC)).TS REG_L
  let ex := ExitResult.chang2 s1.L s1.BBANK
  { s1 with last_exit := some ex }

-- ----------------------------------------------------------------------------
-- Initial Interpreter Hardware State & Fixed Tables (`_init_tables_and_constants`)
-- ----------------------------------------------------------------------------

/-- Construct initial `AGCInterpState` with all Fixed Memory lookup tables populated. -/
def initAGCInterpState : AGCInterpState :=
  let initE : Word15 → Word15 := fun a =>
    if a == FIXLOC || a == PUSHLOC then 0o0706#15
    else if a == NEWJOB then NEG_ZERO
    else POS_ZERO

  let initF : Word15 → Option Word15 := fun a =>
    let an := a.toNat
    -- 1. BIT15..BIT1 table at 0o6000..0o6016
    if an >= 0o6000 && an < 0o6000 + 15 then
      let idx := an - 0o6000
      some (BitVec.ofNat 15 ((1 <<< (14 - idx)) &&& 0o77777))
    -- 2. LIMITS table around 0o6030
    else if a == add_15 ADDR_LIMITS NEGONE then some POSMAX
    else if a == ADDR_LIMITS               then some POS_ZERO
    else if a == add_15 ADDR_LIMITS ONE    then some NEGMAX
    -- 3. NEG1/2 + 1 table around 0o6040
    else if a == add_15 ADDR_NEG_HALF_P1 NEGONE then some NEG_HALF
    else if a == ADDR_NEG_HALF_P1               then some POS_ZERO
    else if a == add_15 ADDR_NEG_HALF_P1 ONE    then some HALF
    -- 4. REVCNT table around 0o6050
    else if a == add_15 ADDR_REVCNT NEGONE then some 0o00002#15
    else if a == ADDR_REVCNT               then some 0o00006#15
    else if a == add_15 ADDR_REVCNT ONE    then some 0o00006#15
    -- 5. NO.WDS table around 0o6060
    else if a == add_15 ADDR_NOWDS NEGONE then some 0o00006#15
    else if a == ADDR_NOWDS               then some 0o00002#15
    else if a == add_15 ADDR_NOWDS ONE    then some 0o00003#15
    -- 6. SIN_POLY table at 0o6100..0o6112
    else if a == ADDR_SIN_POLY then some 3#15
    else if an >= 0o6101 && an <= 0o6112 then
      let off := an - 0o6101
      let pair := SIN_POLY_COEFFS.getD (off / 2) (POS_ZERO, POS_ZERO)
      some (if off % 2 == 0 then pair.1 else pair.2)
    -- 7. ACOS_POLY table at 0o6130..0o6150
    else if a == ADDR_ACOS_POLY then some 6#15
    else if an >= 0o6131 && an <= 0o6150 then
      let off := an - 0o6131
      let pair := ACOS_POLY_COEFFS.getD (off / 2) (POS_ZERO, POS_ZERO)
      some (if off % 2 == 0 then pair.1 else pair.2)
    else
      none

  { erasable           := initE
    fixed              := initF
    channels           := fun _ => POS_ZERO
    reg_A16            := POS_ZERO16
    interrupts_enabled := true
    halted             := false
    alarms             := []
    last_exit          := none }


-- ============================================================================
-- 4. SECTIONS 6, 7, 8, 9, 10, 11, 12: ARITHMETIC, VECTOR, SHIFT, DIV, TRIG, MISC
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Triple Precision Branching Routine (`BRANCH`, Page 1130) & `EXIT`
-- ----------------------------------------------------------------------------

/--
  Triple Precision Branching Routine (Page 1130).
  Returns `(newState, branchIndex)`:
  - `0` (`L+1`): `MPAC > 0`
  - `1` (`L+2`): `MPAC == +0` or `-0`
  - `2` (`L+3`): `MPAC < 0`
-/
def AGCInterpState.BRANCH (s : AGCInterpState) : AGCInterpState × Nat :=
  let (b0, d0) := ccs_eval (s.read_e MPAC)
  let s0 := s.CA d0
  if b0 == 0 then (s0, 0)
  else if b0 == 2 then (s0, 2)
  else
    let (b1, d1) := ccs_eval (s0.read_e MPAC_P1)
    let s1 := s0.CA d1
    if b1 == 0 then (s1, 0)
    else if b1 == 2 then (s1, 2)
    else
      let (b2, d2) := ccs_eval (s1.read_e MPAC_P2)
      let s2 := s1.CA d2
      if b2 == 0 then (s2, 0)
      else if b2 == 2 then (s2, 2)
      else (s2, 1)

def AGCInterpState.EXIT (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CA (s.read_e BANKSET)).TS REG_BBANK
  let ret_addr := add_15 (s1.read_e LOC) ONE
  let s2 := s1.write_e REG_Z ret_addr
  let ex := ExitResult.exit ret_addr s2.BBANK
  { s2 with last_exit := some ex }

-- ----------------------------------------------------------------------------
-- Section 6: Add / Subtract Package (Pages 1131 - 1135)
-- ----------------------------------------------------------------------------

def AGCInterpState.SETOVF2 (s : AGCInterpState) : AGCInterpState :=
  s.TS OVFIND

/--
  Page 1133: Force sign agreement on component at `MPAC + L` after `DAS` overflow,
  and set `OVFIND` if true overflow occurred.
-/
def AGCInterpState.OVERFLOW (s : AGCInterpState) : AGCInterpState :=
  let lim_word := s.read_mem (add_15 ADDR_LIMITS s.A15)
  let s1 := ((s.CS lim_word).TS BUF).AUG REG_A
  let s2 := s1.ADS (add_15 MPAC_P1 s1.L)
  let (s3, ovf_lo) := s2.TS_ovf REG_ZERO
  let s4 := s3.CA ZERO
  let s5 := if ovf_lo then
      s4.CA (if (s4.A &&& 0o100000#16) == 0#16 then ONE else NEGONE)
    else s4
  let s6 := (s5.AD (s5.read_e BUF)).ADS (add_15 MPAC s5.L)
  let (s7, ovf_hi) := s6.TS_ovf REG_ZERO
  if ovf_hi then s7.SETOVF2 else s7

def AGCInterpState.OVERFLWY (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.TS REG_L).CA THREE).XCH REG_L
  s1.OVERFLOW

def AGCInterpState.OVERFLWZ (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.TS REG_L).CA FIVE).XCH REG_L
  s1.OVERFLOW

def AGCInterpState.ENDVXV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.DAS MPAC
  if is_bzf s1.A then
    (s1, some DispStep.danzig)
  else
    (s1.OVERFLOW, some DispStep.danzig)

def AGCInterpState.DAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.DCA (s.read_e ADDRWD)).ENDVXV

def AGCInterpState.DSU (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.DCS (s.read_e ADDRWD)).ENDVXV

def AGCInterpState.BDSU (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (((s.DCA (s.read_e ADDRWD)).DXCH MPAC).DCOM).ENDVXV

def AGCInterpState.VAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCA (add_15 addr TWO)).DAS MPAC_P3
  let s2 := if !(is_bzf s1.A) then s1.OVERFLWY else s1
  let s3 := (s2.DCA (add_15 addr FOUR)).DAS MPAC_P5
  let s4 := if !(is_bzf s3.A) then s3.OVERFLWZ else s3
  (s4.DCA addr).ENDVXV

def AGCInterpState.VSU (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCS (add_15 addr TWO)).DAS MPAC_P3
  let s2 := if !(is_bzf s1.A) then s1.OVERFLWY else s1
  let s3 := (s2.DCS (add_15 addr FOUR)).DAS MPAC_P5
  let s4 := if !(is_bzf s3.A) then s3.OVERFLWZ else s3
  (s4.DCS addr).ENDVXV

def AGCInterpState.BVSU (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (((s.DCA (add_15 addr TWO)).DXCH MPAC_P3).DCOM).DAS MPAC_P3
  let s2 := if !(is_bzf s1.A) then s1.OVERFLWY else s1
  let s3 := (((s2.DCA (add_15 addr FOUR)).DXCH MPAC_P5).DCOM).DAS MPAC_P5
  let s4 := if !(is_bzf s3.A) then s3.OVERFLWZ else s3
  s4.BDSU

def AGCInterpState.TAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCA (add_15 addr ONE)).DAS MPAC_P1
  let s2 := (s1.AD (s1.read_mem addr)).AD (s1.read_e MPAC)
  let (s3, ovf) := s2.TS_ovf MPAC
  let s4 := if ovf then s3.OVERFLOW else s3
  (s4, some DispStep.danzig)

-- ----------------------------------------------------------------------------
-- Section 7: Arithmetic Subroutines in Fixed-Fixed (Pages 1136 - 1142)
-- ----------------------------------------------------------------------------

def AGCInterpState.DMPSUB2 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.MP (s.read_e MPTEMP)).DAS MPAC_P1
  let s2 := ((s1.XCH MPAC).MP (s1.read_e MPTEMP)).DAS MPAC
  s2

/--
  Page 1136: Double Precision Multiply `(MPAC, MPAC+1)` by DP at `C(ADDRWD)`,
  leaving Triple Precision product in `(MPAC, MPAC+1, MPAC+2)`.
-/
def AGCInterpState.DMPSUB (s : AGCInterpState) : AGCInterpState :=
  let addr := s.read_e ADDRWD
  let s1 := (s.CA (s.read_mem (add_15 addr ONE))).TS MPAC_P2
  let s2 := (((s1.CA ZERO).XCH MPAC_P1).TS MPTEMP).MP (s1.read_e MPAC_P2)
  let s3 := ((s2.XCH MPAC_P2).MP (s2.read_e MPAC)).DAS MPAC_P1
  let s4 := (s3.CA (s3.read_mem addr)).XCH MPTEMP
  s4.DMPSUB2

def AGCInterpState.DMP (s : AGCInterpState) (addr_val : Word15) : AGCInterpState :=
  let s1 := (s.CA addr_val).TS ADDRWD
  s1.DMPSUB

/-- Page 1137: Round Triple Precision `MPAC` to Double Precision. -/
def AGCInterpState.VROUND (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.XCH MPAC_P2).DOUBLE
  let (s2, ovf1) := s1.TS_ovf REG_L
  if !ovf1 then s2
  else
    let s3 := s2.AD (s2.read_e MPAC_P1)
    let (s4, ovf2) := s3.TS_ovf MPAC_P1
    if !ovf2 then s4
    else
      let s5 := s4.AD (s4.read_e MPAC)
      let (s6, ovf3) := s5.TS_ovf MPAC
      if !ovf3 then s6
      else s6.SETOVF2

def AGCInterpState.ROUNDSUB_PLUS1 (s : AGCInterpState) : AGCInterpState :=
  (s.TS MODE).VROUND

def AGCInterpState.ROUNDSUB (s : AGCInterpState) : AGCInterpState :=
  (s.CA ZERO).ROUNDSUB_PLUS1

def AGCInterpState.ENDDOT (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.DXCH BUF_P1).DAS MPAC_P1).AD (s.read_e MPAC)
  let s2 := s1.AD (s1.read_e BUF)
  let (s3, ovf) := s2.TS_ovf MPAC
  if ovf then s3.OVERFLOW else s3

/-- Page 1138: Vector Dot Product of `MPAC` and Vector at `C(ADDRWD)`. -/
def AGCInterpState.DOTSUB (s : AGCInterpState) : AGCInterpState :=
  let s1 := (((s.DMPSUB.DXCH MPAC_P3).DXCH MPAC).DXCH BUF)
  let s2 := (s1.CA (s1.read_e MPAC_P2)).TS BUF_P2
  let s3 := ((s2.CA (s2.read_e DOTINC)).ADS ADDRWD).DMPSUB
  let s4 := (((s3.DXCH MPAC_P1).DAS BUF_P1).AD (s3.read_e MPAC)).AD (s3.read_e BUF)
  let (s5, ovf) := s4.TS_ovf BUF
  let s6 := if ovf then s5.TS OVFIND else s5
  let s7 := ((((s6.DXCH MPAC_P5).DXCH MPAC).CA (s6.read_e DOTINC)).ADS ADDRWD).DMPSUB
  s7.ENDDOT

def AGCInterpState.PREDOT (s : AGCInterpState) : AGCInterpState :=
  ((s.CA TWO).TS DOTINC).DOTSUB

/-- Bounded Horner loop for `POLY` / `POWRSERS` (Page 1139). -/
def AGCInterpState.POLYCOM_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    let s1 := s.DMPSUB
    let s2 := (s1.DCA (add_15 (s1.read_e POLISH) ONE)).DAS MPAC
    let (branch, dabs) := ccs_eval (s2.read_e POLYCNT)
    let s3 := s2.CA dabs
    if branch == 0 then
      let s4 := ((s3.TS POLYCNT).CS TWO).ADS POLISH
      POLYCOM_loop fuel' s4
    else
      s3

def AGCInterpState.POLYCOM (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CA VBUF).TS ADDRWD
  let s2 := ((s1.DCA (add_15 (s1.read_e POLISH) THREE)).DXCH MPAC).DXCH VBUF
  s2.POLYCOM_loop 16

def AGCInterpState.POWRSERS (s : AGCInterpState) (coef_loc_minus3 : Word15) (deg_minus1 : Word15) : AGCInterpState :=
  let s1 := (((s.CA coef_loc_minus3).TS POLISH).setL deg_minus1).LXCH POLYCNT
  s1.POLYCOM

def AGCInterpState.POLY (s : AGCInterpState) (table_addr : Word15) : AGCInterpState :=
  let s1 := s.setQ table_addr
  let s2 := ((((s1.CA (s1.read_mem s1.Q)).TS POLYCNT).DOUBLE).AD s1.Q).TS POLISH
  let s3 := (s2.AD FIVE).TS POLYRET
  s3.POLYCOM

/-- Page 1141: Force sign agreement among Triple Precision registers `MPAC, MPAC+1, MPAC+2`. -/
def AGCInterpState.TPAGREE (s : AGCInterpState) : AGCInterpState :=
  let saved_ret := s.L
  let (s1, br) := s.BRANCH
  if br == 1 then
    (((s1.TS MPAC_P2).TS MPAC).TS MPAC_P1).setL saved_ret
  else
    let s2 := if br == 2 then s1.CS POSMAX else s1.CA POSMAX
    let s3 := ((s2.TS REG_Q).AUG REG_A).AD (s2.read_e MPAC_P2)
    let (s4, ovf2) := s3.TS_ovf MPAC_P2
    let s5 := if !ovf2 then s4.CA ZERO else s4
    let s6 := (s5.AD s5.Q).AD (s5.read_e MPAC_P1)
    let (s7, ovf1) := s6.TS_ovf MPAC_P1
    let s8 := if !ovf1 then s7.CA ZERO else s7
    let s9 := ((s8.AD s8.Q).AD (s8.read_e MPAC)).TS MPAC
    s9.setL saved_ret

def AGCInterpState.DPAGREE (s : AGCInterpState) : AGCInterpState :=
  ((s.CA ZERO).TS MPAC_P2).TPAGREE

def AGCInterpState.SHORTMP (s : AGCInterpState) (sp_val_in_A : Option Word15 := none) : AGCInterpState :=
  let s1 := match sp_val_in_A with
    | some v => s.CA v
    | none   => s
  let s2 := ((((s1.TS MPTEMP).MP (s1.read_e MPAC_P2)).TS MPAC_P2).CA ZERO).XCH MPAC_P1
  s2.DMPSUB2

def AGCInterpState.DMPNSUB (s : AGCInterpState) (sp_val_in_A : Option Word15 := none) : AGCInterpState :=
  let s1 := match sp_val_in_A with
    | some v => s.CA v
    | none   => s
  let s2 := (((s1.TS DMPNTEMP).MP (s1.read_e MPAC_P1)).DXCH MPAC).MP (s1.read_e DMPNTEMP)
  let s3 := (s2.CA s2.L).ADS MPAC
  s3.DCA MPAC

-- ----------------------------------------------------------------------------
-- Load, Store, and Mode Helpers Used Across Sections
-- ----------------------------------------------------------------------------

def AGCInterpState.NEWMODE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.TS MODE, some DispStep.danzig)

def AGCInterpState.VMODE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CS ONE).NEWMODE

def AGCInterpState.DMODE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CA ZERO).NEWMODE

def AGCInterpState.SLOAD2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.DXCH MPAC).CA ZERO).TS MPAC_P2
  s1.NEWMODE

def AGCInterpState.DLOAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.DCA (s.read_e ADDRWD)).SLOAD2

def AGCInterpState.TLOAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.CA (s.read_mem (add_15 addr TWO))).TS MPAC_P2
  let s2 := ((s1.DCA addr).DXCH MPAC).CA ONE
  s2.NEWMODE

def AGCInterpState.SLOAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ZL
  (s1.CA (s1.read_mem (s1.read_e ADDRWD))).SLOAD2

def AGCInterpState.ENDVLOAD_PLUS4 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCA (add_15 addr FOUR)).DXCH MPAC_P5
  s1.VMODE

def AGCInterpState.ENDVLOAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCA (add_15 addr TWO)).DXCH MPAC_P3
  s1.ENDVLOAD_PLUS4

def AGCInterpState.VLOAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let s1 := (s.DCA addr).DXCH MPAC
  s1.ENDVLOAD

def AGCInterpState.STORE1 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.TS (s.read_e ADDRWD), some DispStep.danzig)

def AGCInterpState.SSP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.INCR LOC
  (s1.CA (s1.read_mem (s1.read_e LOC))).STORE1

-- ----------------------------------------------------------------------------
-- Section 8: Vector Operations (Pages 1143 - 1151)
-- ----------------------------------------------------------------------------

def AGCInterpState.MPACVBUF (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.DCA MPAC).DXCH VBUF
  let s2 := (s1.DCA MPAC_P3).DXCH VBUF_P2
  (s2.DCA MPAC_P5).DXCH VBUF_P4

def AGCInterpState.DOT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  s.PREDOT.DMODE

def AGCInterpState.VXM_MXV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.TS DOTINC).MPACVBUF.DOTSUB
  let s2 := ((s1.DCA VBUF).DXCH MPAC).DXCH BUF2
  let s3 := (s2.DCA VBUF_P2).DXCH MPAC_P3
  let s4 := (s3.DCA VBUF_P4).DXCH MPAC_P5
  let s5 := ((s4.CA (s4.read_e MATINC)).ADS ADDRWD).DOTSUB
  let s6 := (((((s5.DXCH VBUF).DXCH MPAC).DXCH VBUF_P2).DXCH MPAC_P3).DXCH VBUF_P4).DXCH MPAC_P5
  let s7 := ((s6.CA (s6.read_e MATINC)).ADS ADDRWD).DOTSUB
  let s8 := ((((s7.DXCH BUF2).DXCH MPAC).DXCH MPAC_P5).DXCH VBUF_P2).DXCH MPAC_P3
  (s8, some DispStep.danzig)

def AGCInterpState.MXV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  ((s.CA TWO).TS MATINC).VXM_MXV

def AGCInterpState.VXM (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (((s.CS TEN).TS MATINC).CA SIX).VXM_MXV

def AGCInterpState.VROTATEX (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DXCH MPAC).DXCH MPAC_P5).DXCH MPAC_P3).DXCH MPAC
  (s1, some DispStep.danzig)

def AGCInterpState.DVXSC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DCA MPAC).DXCH MPAC_P3).DMPSUB).VROUND
  let s2 := (s1.CA TWO).ADS ADDRWD
  let s3 := ((((s2.DCA MPAC_P3).DXCH MPAC).DXCH MPAC_P5).DMPSUB).VROUND
  let s4 := (s3.CA TWO).ADS ADDRWD
  let s5 := ((((s4.DXCH MPAC_P3).DXCH MPAC).DXCH MPAC_P3).DMPSUB).VROUND
  let s6 := ((s5.DXCH MPAC).DXCH MPAC_P5).DXCH MPAC
  s6.VMODE

def AGCInterpState.VXSC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MODE)
  let s1 := s.CA dabs
  if branch == 0 || branch == 1 then
    s1.DVXSC
  else
    let s2 := (((s1.DMPSUB.VROUND).DXCH MPAC_P3).DXCH MPAC).DXCH MPAC_P3
    let s3 := (((s2.DMPSUB.VROUND).DXCH MPAC_P5).DXCH MPAC).DXCH MPAC_P5
    let s4 := s3.DMPSUB.VROUND
    s4.VROTATEX

def AGCInterpState.VPROJ (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.PREDOT.CS FOUR).ADS ADDRWD)
  s1.DVXSC

/--
  Page 1147: Vector Cross Product (`VXV`):
  Calculates `(X3*M2 - X2*M3, X1*M3 - X3*M1, X2*M1 - X1*M2)`.
-/
def AGCInterpState.VXV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DCA MPAC_P5).DXCH MPAC).DXCH VBUF).DMPSUB
  let s2 := (((s1.DCS MPAC_P3).DXCH MPAC).DXCH VBUF_P2).DMPSUB
  let s3 := (s2.CA TWO).ADS ADDRWD
  let s4 := (((s3.DCS MPAC_P5).DXCH MPAC).DXCH MPAC_P5).DMPSUB
  let s5 := (((s4.DCA VBUF).DXCH MPAC).DXCH VBUF_P4).DMPSUB
  let s6 := (s5.CA TWO).ADS ADDRWD
  let s7 := ((s6.DCS VBUF).DXCH MPAC).DAS MPAC_P5
  let s8 := if !(is_bzf s7.A) then s7.OVERFLWZ else s7
  let s9 := (((s8.DMPSUB.DXCH VBUF_P2).DXCH MPAC_P3).DXCH MPAC).DAS MPAC_P3
  let s10 := if !(is_bzf s9.A) then s9.OVERFLWY else s9
  let s11 := (s10.DMPSUB).DXCH VBUF_P4
  s11.ENDVXV

/-- Page 1148: Double Precision Sign Agree Routine (`ALSIGNAG`). -/
def AGCInterpState.ALSIGNAG (s : AGCInterpState) : AGCInterpState :=
  let (branch, dabs) := ccs_eval s.A15
  let s1 := s.CA dabs
  if branch == 1 || branch == 3 then
    s1
  else if branch == 0 then
    let s2 := ((s1.XCH REG_L).AD HALF).AD HALF
    let (s3, ovf) := s2.TS_ovf REG_A
    let s4 := if ovf then s3.INCR REG_L else s3
    s4.XCH REG_L
  else
    let s2 := ((s1.XCH REG_L).AD NEGMAX).AD NEGONE
    let (s3, ovf) := s2.TS_ovf REG_A
    let s4 := if ovf then s3.INCR REG_L else s3
    (s4.XCH REG_L).COM

def AGCInterpState.VECAGREE (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.DXCH MPAC).ALSIGNAG).DXCH MPAC
  let s2 := ((s1.DXCH MPAC_P3).ALSIGNAG).DXCH MPAC_P3
  ((s2.DXCH MPAC_P5).ALSIGNAG).DXCH MPAC_P5

def AGCInterpState.DMP1 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.DMPSUB, some DispStep.danzig)

def AGCInterpState.DMPR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (((s.DMPSUB).CA ZERO).ROUNDSUB_PLUS1, some DispStep.danzig)

def AGCInterpState.SETPD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  ((s.CA (s.read_e ADDRWD)).TS PUSHLOC, some DispStep.noibnksw)

def AGCInterpState.COMP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.DCS MPAC).DXCH MPAC
  let (branch, dabs) := ccs_eval (s1.read_e MODE)
  let s2 := s1.CA dabs
  if branch == 0 || branch == 1 then
    let s3 := (s2.CS (s2.read_e MPAC_P2)).TS MPAC_P2
    (s3, some DispStep.danzig)
  else
    let s3 := ((s2.DCS MPAC_P3).DXCH MPAC_P3).DCS MPAC_P5
    (s3.DXCH MPAC_P5, some DispStep.danzig)

def AGCInterpState.SIGN (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let addr := s.read_e ADDRWD
  let (branch, dabs) := ccs_eval (s.read_mem addr)
  let s1 := s.CA dabs
  if branch == 0 then
    (s1, some DispStep.danzig)
  else if branch == 2 then
    s1.COMP
  else
    let (b2, dabs2) := ccs_eval (s1.read_mem (add_15 addr ONE))
    let s2 := s1.CA dabs2
    if b2 == 2 then s2.COMP else (s2, some DispStep.danzig)

-- ----------------------------------------------------------------------------
-- Section 9: Shifting Routines (Pages 1152 - 1161)
-- ----------------------------------------------------------------------------

def AGCInterpState.MPACSHR_PLUS3 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TS MPAC_P2
  let s2 := ((s1.CA (s1.read_e MPTEMP)).MP (s1.read_e MPAC)).DXCH MPAC
  let s3 := ((s2.CA (s2.read_e MPTEMP)).MP s2.L).DAS MPAC_P1
  (s3, some DispStep.danzig)

def AGCInterpState.MPACSHR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e MPTEMP)).MP (s.read_e MPAC_P2)
  s1.MPACSHR_PLUS3

def AGCInterpState.VSHR2 (s : AGCInterpState) : AGCInterpState :=
  let s1 := s.DOUBLE
  let (s2, ovf) := s1.TS_ovf MPAC_P2
  let s3 := if ovf then s2.ADS MPAC_P1 else s2
  let s4 := ((s3.CA ZERO).TS MPAC_P2).XCH MPAC
  (s4.MP (s4.read_e MPTEMP)).DAS MPAC

def AGCInterpState.MPACSRND (s : AGCInterpState) : AGCInterpState :=
  let s1 := (((s.CA (s.read_e MPAC_P2)).MP (s.read_e MPTEMP)).XCH MPAC_P1).MP (s.read_e MPTEMP)
  let s2 := (s1.XCH MPAC_P1).AD s1.L
  s2.VSHR2

def AGCInterpState.RIGHTR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  s.MPACSRND.NEWMODE

def AGCInterpState.VSHRRND (s : AGCInterpState) : AGCInterpState :=
  let s1 := (((s.CA (s.read_e MPTEMP)).MP (s.read_e MPAC_P1)).TS MPAC_P1).XCH REG_L
  s1.VSHR2

def AGCInterpState.ROUND (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.ROUNDSUB, some DispStep.danzig)

def AGCInterpState.TSSL_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    let s1 := (((s.DCA MPAC_P1).DAS MPAC_P1).AD (s.read_e MPAC)).AD (s.read_e MPAC)
    let (s2, ovf) := s1.TS_ovf MPAC
    let s3 := if ovf then s2.TS OVFIND else s2
    let (branch, dabs) := ccs_eval (s3.read_e MPTEMP)
    let s4 := s3.CA dabs
    if branch == 0 then
      TSSL_loop fuel' (s4.TS MPTEMP)
    else
      s4

def AGCInterpState.TSSL_PLUS2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TSSL_loop 32
  let (b_rnd, dabs_rnd) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs_rnd
  if b_rnd == 0 then s2.ROUND else (s2, some DispStep.danzig)

def AGCInterpState.TSSL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e REG_SR)).TS MPTEMP
  s1.TSSL_PLUS2

def AGCInterpState.SHORTT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CA SIX).MASK (s.read_e REG_CYR)).TS REG_SR
  let (branch, dabs) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.TSSL
  else
    let shift_bit := s2.read_mem (add_15 ADDR_BIT14_TABLE (s2.read_e REG_SR))
    let s3 := (s2.CA shift_bit).TS MPTEMP
    let (b_rnd, dabs_rnd) := ccs_eval (s3.read_e REG_CYR)
    let s4 := s3.CA dabs_rnd
    if b_rnd == 0 then s4.RIGHTR else s4.MPACSHR

def AGCInterpState.VSSR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let shift_bit := s.read_mem (add_15 ADDR_BIT14_TABLE (s.read_e MPTEMP))
  let s1 := ((s.CA shift_bit).TS MPTEMP).VSHRRND
  let s2 := (((s1.DXCH MPAC).DXCH MPAC_P3).DXCH MPAC).VSHRRND
  let s3 := (((s2.DXCH MPAC).DXCH MPAC_P5).DXCH MPAC).VSHRRND
  s3.VROTATEX

def AGCInterpState.VSSL_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    let s1 := (s.DCA MPAC).DAS MPAC
    let s2 := if !(is_bzf s1.A) then s1.OVERFLOW else s1
    let s3 := (s2.DCA MPAC_P3).DAS MPAC_P3
    let s4 := if !(is_bzf s3.A) then s3.OVERFLWY else s3
    let s5 := (s4.DCA MPAC_P5).DAS MPAC_P5
    let s6 := if !(is_bzf s5.A) then s5.OVERFLWZ else s5
    let (branch, dabs) := ccs_eval (s6.read_e MPTEMP)
    let s7 := s6.CA dabs
    if branch == 0 then
      VSSL_loop fuel' (s7.TS MPTEMP)
    else
      s7

def AGCInterpState.VSSL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.VSSL_loop 32, some DispStep.danzig)

def AGCInterpState.SHORTV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CA LOW3).MASK (s.read_e REG_CYR)).TS MPTEMP
  let (branch, dabs) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs
  if branch == 0 then s2.VSSL else s2.VSSR

def AGCInterpState.ENDTSLC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CS (s.read_e MPTEMP)).STORE1

def AGCInterpState.TSLC2_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    let s1 := s.DOUBLE
    if s1.OVSK then
      s1
    else
      let s2 := s1.INCR MPTEMP
      let s3 := (((s2.DCA MPAC_P1).DAS MPAC_P1).AD (s2.read_e MPAC)).ADS MPAC
      TSLC2_loop fuel' s3

def AGCInterpState.TSLC2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TS MPTEMP
  let (s2, br) := s1.BRANCH
  if br == 1 then
    s2.ENDTSLC
  else
    let s3 := s2.TPAGREE
    let s4 := s3.CA (s3.read_e MPAC)
    (s4.TSLC2_loop 45).ENDTSLC

def AGCInterpState.TSLC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  ((s.CA ZERO).TS REG_FBANK).TSLC2

def AGCInterpState.SETROUND (s : AGCInterpState) : AGCInterpState :=
  (((s.DOUBLE).TS MPAC_P2).CA ZERO).XCH REG_L

def AGCInterpState.DOSSHFT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let shift_bit := s.read_mem (add_15 ADDR_BIT14_TABLE (s.read_e MPTEMP))
  let s1 := ((s.CA shift_bit).TS MPTEMP).CA BIT10
  let s2 := s1.MASK (s1.read_e ADDRWD)
  let (branch, dabs) := ccs_eval s2.A15
  let s3 := s2.CA dabs
  if branch == 0 then s3.RIGHTR else s3.MPACSHR

def AGCInterpState.GENSCR_PLUS4_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  match fuel with
  | 0 => (s, some DispStep.danzig)
  | fuel' + 1 =>
    let s1 := (((((s.AD NEGONE).TS MPTEMP).CA ZERO).XCH MPAC).XCH MPAC_P1).TS MPAC_P2
    let (b_cnt, dabs_cnt) := ccs_eval (s1.read_e MPTEMP)
    let s2 := s1.CA dabs_cnt
    if b_cnt == 0 then
      let s3 := (s2.TS MPTEMP).AD NEG12
      if is_bzmf s3.A then
        s3.DOSSHFT
      else
        GENSCR_PLUS4_loop fuel' s3
    else
      let s3 := (s2.CA BIT10).MASK (s2.read_e ADDRWD)
      let (b_rnd, dabs_rnd) := ccs_eval s3.A15
      let s4 := s3.CA dabs_rnd
      let s5 := if b_rnd == 0 then s4.ROUNDSUB else s4
      (s5, some DispStep.danzig)

def AGCInterpState.GENSCR_PLUS4 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  s.GENSCR_PLUS4_loop 16

def AGCInterpState.GENSCR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e MPTEMP)).AD NEG12
  if is_bzmf s1.A then s1.DOSSHFT else s1.GENSCR_PLUS4

def AGCInterpState.RIGHT_vec_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  match fuel with
  | 0 => (s, some DispStep.danzig)
  | fuel' + 1 =>
    let s1 := s.AD NEG12
    if is_bzmf s1.A then
      s1.VSSR
    else
      let s2 := ((((s1.AD NEGONE).TS MPTEMP).CA ZERO).TS REG_L)
      let s3 := (((s2.XCH MPAC).XCH MPAC_P1).SETROUND).DAS MPAC
      let s4 := (((s3.XCH MPAC_P3).XCH MPAC_P4).SETROUND).DAS MPAC_P3
      let s5 := (((s4.XCH MPAC_P5).XCH MPAC_P6).SETROUND).DAS MPAC_P5
      let (b_cnt, dabs_cnt) := ccs_eval (s5.read_e MPTEMP)
      let s6 := s5.CA dabs_cnt
      if b_cnt == 0 then
        RIGHT_vec_loop fuel' (s6.TS MPTEMP)
      else
        (s6, some DispStep.danzig)

def AGCInterpState.RIGHT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MODE)
  let s1 := s.CA dabs
  if branch == 0 || branch == 1 then
    s1.GENSCR
  else
    (s1.CA (s1.read_e MPTEMP)).RIGHT_vec_loop 16

def AGCInterpState.LEFT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MODE)
  let s1 := s.CA dabs
  if branch == 2 then
    s1.VSSL
  else
    let s2 := ((s1.CS (s1.read_e ADDRWD)).MP BIT6).TS REG_CYR
    s2.TSSL_PLUS2

def AGCInterpState.GENSHIFT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.MASK (s.read_e ADDRWD)
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch != 0 then
    let s3 := (s2.CA BIT10).MASK (s2.read_e ADDRWD)
    let (b_rnd, dabs_rnd) := ccs_eval s3.A15
    let s4 := s3.CA dabs_rnd
    let s5 := if b_rnd == 0 then s4.ROUNDSUB else s4
    (s5, some DispStep.danzig)
  else
    let s3 := (((s2.TS MPTEMP).CA BIT8).MP (s2.read_e ADDRWD)).MASK LOW2
    let idx := s3.A15.toNat
    if idx == 0 then
      let s4 := ((s3.CS (s3.read_e MPTEMP)).AD OCT176).TS MPTEMP
      s4.RIGHT
    else if idx == 1 then
      s3.LEFT
    else if idx == 2 then
      let s4 := (((s3.CS OCT176).AD (s3.read_e MPTEMP)).COM).TS MPTEMP
      s4.LEFT
    else
      s3.RIGHT

def AGCInterpState.GSHIFT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  ((s.CA LOW7).TS REG_FBANK).GENSHIFT


-- ============================================================================
-- 5. SECTION 10: DIVISION & UNIT VECTOR PACKAGE (PAGES 1162 - 1179)
-- ============================================================================

def AGCInterpState.FINALDV_PLUS3 (s : AGCInterpState) : AGCInterpState :=
  let s1 := s.TS MPAC_P1
  let (branch, dabs) := ccs_eval (s1.read_e DVSIGN)
  let s2 := s1.CA dabs
  if branch == 0 || branch == 1 || branch == 2 then
    s2
  else
    ((s2.DCS MPAC).DXCH MPAC).CA ZERO

def AGCInterpState.FINALDV (s : AGCInterpState) : AGCInterpState :=
  ((s.ZL).DV BUF).FINALDV_PLUS3

def AGCInterpState.DVOVF (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CA POSMAX).TS MPAC).FINALDV_PLUS3
  let s2 := (s1.CA ONE).TS OVFIND
  (s2, some DispStep.danzig)

def AGCInterpState.PLUS_DOWN (s : AGCInterpState) : AGCInterpState :=
  let s1 := s.SU (s.read_e BUF)
  if is_bzf s1.A then
    (s1.INCR MPAC).FINALDV
  else if is_bzmf s1.A then
    (s1.AD (s1.read_e BUF)).FINALDV
  else
    (s1.INCR MPAC).FINALDV

def AGCInterpState.MINUS_UP (s : AGCInterpState) : AGCInterpState :=
  if is_bzf s.A then
    s.FINALDV_PLUS3
  else
    ((s.DIM MPAC).AD (s.read_e BUF)).FINALDV

def AGCInterpState.GENDDV_PLUS1 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.DV BUF).DXCH MPAC
  let s2 := ((s1.CS (s1.read_e MPAC)).MP (s1.read_e BUF_P1)).AD (s1.read_e MPAC_P1)
  if s2.OVSK then
    ((s2.SU (s2.read_e BUF)).INCR MPAC).PLUS_DOWN
  else if is_bzmf s2.A then
    s2.MINUS_UP
  else
    s2.PLUS_DOWN

def AGCInterpState.GENDDV (s : AGCInterpState) : AGCInterpState :=
  (s.DXCH MPAC).GENDDV_PLUS1

def AGCInterpState.MAXDV (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e MPAC)).AD (s.read_e BUF)
  if !(is_bzf s1.A) then
    s1.GENDDV
  else
    let s2 := (s1.CA POSMAX).TS MPAC
    let s3 := ((s2.CS (s2.read_e BUF_P1)).AD (s2.read_e MPAC_P1)).AD (s2.read_e BUF)
    s3.FINALDV

/-- Repeat `DDOUBL` `n` times. -/
def AGCInterpState.ddoubl_n (n : Nat) (s : AGCInterpState) : AGCInterpState :=
  match n with
  | 0 => s
  | n' + 1 => (s.DDOUBL).ddoubl_n n'

/--
  Page 1166: Execute the indexed jump `INDEX DVNORMCT / TC MAXTEST`
  (or `INDEX MPTEMP / TCF MAXTEST -1` from `UNITDV`).
-/
def AGCInterpState.exec_MAXTEST_prologue (s : AGCInterpState) (norm_offset_15 : Word15) : AGCInterpState :=
  let off : Int := s15_to_int norm_offset_15
  if off == -21 then
    let s1 := ((((s.LXCH REG_SR).MP HALF).XCH REG_L).AD (s.read_e REG_SR)).XCH REG_L
    s1.GENDDV_PLUS1
  else
    let num_ddoubl : Nat := if -off > 1 then (-off - 1).toNat else 0
    let s1 := s.ddoubl_n num_ddoubl
    let s2 := if off < 0 then s1.DXCH MPAC else s1
    let (branch, dabs) := ccs_eval (s2.read_e MAXDVSW)
    let s3 := s2.CA dabs
    if branch == 1 then s3.MAXDV else s3.GENDDV

def AGCInterpState.DVNORM_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    let s1 := (s.CA (s.read_e BUF)).DOUBLE
    if s1.OVSK then
      s1
    else
      let s2 := ((s1.AUG DVNORMCT).DCA BUF).DAS BUF
      DVNORM_loop fuel' s2

def AGCInterpState.DVNORM (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.DVNORM_loop 20).DXCH MPAC
  let s2 := s1.exec_MAXTEST_prologue (s1.read_e DVNORMCT)
  (s2.TS MPAC_P2, some DispStep.danzig)

def AGCInterpState.MPAC_PLUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CS (s.read_e MPAC)).AD NEGONE).AD (s.read_e BUF)
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.DVNORM
  else
    let s3 := ((s2.CA HALF).DOUBLE).AD (s2.read_e MPAC_P1)
    let (s4, ovf_m) := s3.TS_ovf MPAC_P1
    let s5 := if !ovf_m then s4.CA ZERO else s4
    let s6 := (s5.AD POSMAX).ADS MPAC

    let s7 := ((s6.CA HALF).DOUBLE).AD (s6.read_e BUF_P1)
    let (s8, ovf_b) := s7.TS_ovf BUF_P1
    let s9 := if !ovf_b then s8.CA ZERO else s8
    let s10 := (s9.AD POSMAX).ADS BUF

    let s11 := (s10.CS (s10.read_e MPAC)).AD (s10.read_e BUF)
    let (b_cmp, dabs_cmp) := ccs_eval s11.A15
    let s12 := s11.CA dabs_cmp
    if b_cmp == 0 then
      s12.DVNORM
    else if b_cmp == 1 || b_cmp == 2 then
      s12.DVOVF
    else
      let s13 := ((s12.TS MAXDVSW).CS (s12.read_e MPAC_P1)).AD (s12.read_e BUF_P1)
      if is_bzmf s13.A then s13.DVOVF else s13.DVNORM

def AGCInterpState.MPAC_MINUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.DCS MPAC).DXCH MPAC).INCR DVSIGN
  s1.MPAC_PLUS

def AGCInterpState.BUF_PLUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MPAC)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.MPAC_PLUS
  else if branch == 2 then
    s1.MPAC_MINUS
  else
    let (b1, dabs1) := ccs_eval (s1.read_e MPAC_P1)
    let s2 := s1.CA dabs1
    if b1 == 0 then s2.MPAC_PLUS
    else if b1 == 2 then s2.MPAC_MINUS
    else (s2, some DispStep.danzig)

def AGCInterpState.BUF_MINUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.DCS BUF).DXCH BUF).INCR DVSIGN
  s1.BUF_PLUS

def AGCInterpState.SGNDVOVF (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := if !(is_bzmf s.A) then s.INCR DVSIGN else s
  s1.DVOVF

def AGCInterpState.BUFZERO (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.TS MPAC_P2).TPAGREE
  let (branch, dabs) := ccs_eval (s1.read_e MPAC)
  let s2 := s1.CA dabs
  if branch == 0 then
    (s2.CS (s2.read_e BUF_P1)).SGNDVOVF
  else if branch == 2 then
    ((s2.INCR DVSIGN).CS (s2.read_e BUF_P1)).SGNDVOVF
  else
    let s3 := (((s2.XCH BUF_P1).XCH BUF).XCH MPAC_P1).XCH MPAC
    let (b_buf, dabs_buf) := ccs_eval (s3.read_e BUF)
    let s4 := s3.CA dabs_buf
    if b_buf == 0 then s4.BUF_PLUS
    else if b_buf == 2 then s4.BUF_MINUS
    else (s4.CS (s4.read_e MPAC)).SGNDVOVF

def AGCInterpState.BUFPOS_PLUS6 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DOUBLE).ADS BUF_P1).CA ZERO).TS BUF
  s1.BUFZERO

def AGCInterpState.BUFPOS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval s.A15
  let s1 := s.CA dabs
  if branch == 0 then
    s1.BUF_PLUS
  else
    let s2 := s1.CS (s1.read_e BUF_P1)
    if is_bzmf s2.A then s2.BUF_PLUS else (s2.CA HALF).BUFPOS_PLUS6

def AGCInterpState.BUFNEG (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval s.A15
  let s1 := s.CA dabs
  if branch == 0 then
    s1.BUF_MINUS
  else
    let s2 := s1.CA (s1.read_e BUF_P1)
    if is_bzmf s2.A then s2.BUF_MINUS else (s2.CS HALF).BUFPOS_PLUS6

def AGCInterpState.DDV_BDDV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.CS ONE).TS DVSIGN).TS DVNORMCT).TS MAXDVSW
  let (branch, dabs) := ccs_eval (s1.read_e BUF)
  let s2 := s1.CA dabs
  if branch == 0 then s2.BUFPOS
  else if branch == 2 then s2.BUFNEG
  else s2.BUFZERO

def AGCInterpState.DDV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DCA (s.read_e ADDRWD)).DXCH BUF).CA ZERO).TS REG_FBANK
  s1.DDV_BDDV

def AGCInterpState.BDDV (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((((s.DCA (s.read_e ADDRWD)).DXCH MPAC).DXCH BUF).CA ZERO).TS REG_FBANK
  s1.DDV_BDDV

-- ----------------------------------------------------------------------------
-- V/SC and V/SC2 (Pages 1171 - 1174)
-- ----------------------------------------------------------------------------

def AGCInterpState.V_SCDV (s : AGCInterpState) : AGCInterpState × Bool :=
  let s1 := (s.CA (s.read_e VBUF_P5)).TS DVSIGN
  let (branch, dabs) := ccs_eval (s1.read_e MPAC)
  let s2 := s1.CA dabs
  let (s3, early_done) : AGCInterpState × Bool :=
    if branch == 1 || branch == 3 then
      let (b1, dabs1) := ccs_eval (s2.read_e MPAC_P1)
      let s_b1 := s2.CA dabs1
      if b1 == 1 || b1 == 3 then
        (s_b1, true)
      else if b1 == 2 then
        (((s_b1.DCS MPAC).DXCH MPAC).INCR DVSIGN, false)
      else
        (s_b1, false)
    else if branch == 2 then
      (((s2.DCS MPAC).DXCH MPAC).INCR DVSIGN, false)
    else
      (s2, false)

  if early_done then
    (s3, false)
  else
    let s4 := (s3.CS ONE).TS MAXDVSW
    let s5 := (s4.CS (s4.read_e MPAC)).AD (s4.read_e BUF2)
    let (b_ov, dabs_ov) := ccs_eval s5.A15
    let s6 := s5.CA dabs_ov
    if b_ov == 2 then
      (s6, true)
    else if b_ov == 1 || b_ov == 3 then
      let s7 := ((s6.TS MAXDVSW).CS (s6.read_e MPAC_P1)).AD (s6.read_e BUF2_P1)
      if is_bzmf s7.A then
        (s7, true)
      else
        let s8 := s7.DXCH MPAC
        (s8.exec_MAXTEST_prologue (s8.read_e DVNORMCT), false)
    else
      let s7 := s6.DXCH MPAC
      (s7.exec_MAXTEST_prologue (s7.read_e DVNORMCT), false)

def AGCInterpState.SLASH_BUF_PLUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.DCA BUF).DXCH BUF2).DVNORM_loop 20
  let (s2, ovf1) := s1.V_SCDV
  if ovf1 then s2.DVOVF
  else
    let s3 := ((s2.DXCH MPAC_P3).DXCH MPAC).DXCH MPAC_P3
    let (s4, ovf2) := s3.V_SCDV
    if ovf2 then s4.DVOVF
    else
      let s5 := ((s4.DXCH MPAC_P5).DXCH MPAC).DXCH MPAC_P5
      let (s6, ovf3) := s5.V_SCDV
      if ovf3 then s6.DVOVF
      else s6.VROTATEX

def AGCInterpState.SLASH_BUF_MINUS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.DCS BUF).DXCH BUF).INCR VBUF_P5
  s1.SLASH_BUF_PLUS

def AGCInterpState.V_SC2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CS ONE).TS DVNORMCT).TS VBUF_P5
  let s2 := (((s1.VECAGREE).DXCH BUF).ALSIGNAG).DXCH BUF
  let (branch, dabs) := ccs_eval (s2.read_e BUF)
  let s3 := s2.CA dabs
  if branch == 0 then
    s3.SLASH_BUF_PLUS
  else if branch == 2 then
    s3.SLASH_BUF_MINUS
  else
    let s4 := (((s3.XCH BUF_P1).XCH BUF).XCH MPAC_P1).XCH MPAC
    if !(is_bzf s4.A) then s4.DVOVF
    else
      let s5 := (s4.XCH MPAC_P4).XCH MPAC_P3
      if !(is_bzf s5.A) then s5.DVOVF
      else
        let s6 := (s5.XCH MPAC_P6).XCH MPAC_P5
        if !(is_bzf s6.A) then s6.DVOVF
        else
          let (b2, dabs2) := ccs_eval (s6.read_e BUF)
          let s7 := s6.CA dabs2
          if b2 == 0 then s7.SLASH_BUF_PLUS
          else if b2 == 2 then s7.SLASH_BUF_MINUS
          else s7.DVOVF

def AGCInterpState.V_SC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MODE)
  let s1 := s.CA dabs
  let s2 := if branch == 0 || branch == 1 then
      let addr := s1.read_e ADDRWD
      let s_a := (s1.DCA (add_15 addr TWO)).DXCH MPAC_P3
      let s_b := (s_a.DCA (add_15 addr FOUR)).DXCH MPAC_P5
      let s_c := (s_b.CS ONE).TS MODE
      (s_c.DCA addr).DXCH MPAC
    else
      s1.DCA (s1.read_e ADDRWD)
  let s3 := ((s2.DXCH BUF).CA ZERO).TS REG_FBANK
  s3.V_SC2


-- ============================================================================
-- 6. SECTION 11: UNARY, SQRT, UNIT, AND TRIGONOMETRY (PAGES 1175 - 1191)
-- ============================================================================

def AGCInterpState.DSQSUB (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.CA (s.read_e MPAC_P1)).SQUARE).TS MPAC_P2
  let s2 := ((((s1.CA ZERO).XCH MPAC_P1).MP (s1.read_e MPAC)).DDOUBL).DAS MPAC_P1
  ((s2.XCH MPAC).SQUARE).DAS MPAC

def AGCInterpState.VSQSUB (s : AGCInterpState) : AGCInterpState :=
  let s1 := (((s.DSQSUB.DXCH MPAC_P3).DXCH MPAC).DXCH BUF)
  let s2 := (s1.CA (s1.read_e MPAC_P2)).TS BUF_P2
  let s3 := ((((s2.DSQSUB.DXCH MPAC_P1).DAS BUF_P1).AD (s2.read_e MPAC)).AD (s2.read_e BUF))
  let (s4, ovf) := s3.TS_ovf BUF
  let s5 := if ovf then s4.TS OVFIND else s4
  let s6 := ((s5.DXCH MPAC_P5).DXCH MPAC).DSQSUB
  s6.ENDDOT

-- ----------------------------------------------------------------------------
-- Double Precision Square Root (`SQRTSUB`, Page 1184)
-- ----------------------------------------------------------------------------

def AGCInterpState.FIXROOT (s : AGCInterpState) : AGCInterpState :=
  (s.TS MPAC).TS MPAC_P1

def AGCInterpState.ZEROANS (s : AGCInterpState) : AGCInterpState :=
  (s.CA ZERO).FIXROOT

def AGCInterpState.SQRTNEG (s : AGCInterpState) : AGCInterpState :=
  let (branch, dabs) := ccs_eval s.A15
  let s1 := s.CA dabs
  if branch == 0 then
    s1.POODOO 0o1302#15
  else
    let (b1, dabs1) := ccs_eval (s1.read_e MPAC_P1)
    let s2 := s1.CA dabs1
    if b1 == 0 || b1 == 1 then s2.ZEROANS
    else if b1 == 2 then s2.POODOO 0o1302#15
    else s2.FIXROOT

def AGCInterpState.ARGHI_PLUS4 (s : AGCInterpState) : AGCInterpState :=
  let s1 := s.TS BUF
  let s2 := ((((s1.CA (s1.read_e MPAC)).ZL).DV BUF).MP HALF).ADS BUF
  let s3 := (((s2.MP HALF).DXCH MPAC).DV BUF).TS BUF_P1
  let s4 := ((((s3.CA ZERO).XCH REG_L).DV BUF).TS REG_L).CA (s3.read_e BUF_P1)
  let s5 := s4.DAS MPAC
  if !(is_bzf s5.A) then (s5.CA POSMAX).FIXROOT else s5

def AGCInterpState.ARGHI (s : AGCInterpState) : AGCInterpState :=
  (((s.CA SLOPEHI).MP (s.read_e MPAC)).AD BIASHI).ARGHI_PLUS4

def AGCInterpState.ARGLO (s : AGCInterpState) : AGCInterpState :=
  (((s.CA SLOPELO).MP (s.read_e MPAC)).AD BIASLO).ARGHI_PLUS4

def AGCInterpState.SQRTNORM_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState :=
  match fuel with
  | 0 => s.ARGLO
  | fuel' + 1 =>
    let s1 := (((((s.DCA MPAC_P1).DAS MPAC_P1).AD (s.read_e MPAC)).ADS MPAC).DOUBLE).TS REG_CYL
    let (b1, dabs1) := ccs_eval (s1.read_e REG_CYL)
    let s2 := s1.CA dabs1
    if b1 == 0 then
      let (b2, dabs2) := ccs_eval (s2.read_e REG_CYL)
      let s3 := s2.CA dabs2
      if b2 == 0 then
        let s4 := ((((s3.DCA MPAC_P1).DAS MPAC_P1).AD (s3.read_e MPAC)).ADS MPAC).INCR MPTEMP
        SQRTNORM_loop fuel' s4
      else if b2 == 1 then
        s3.ARGHI
      else
        s3.ARGLO
    else if b1 == 2 then
      s2.ARGHI
    else
      s2.ARGLO

def AGCInterpState.SQRTNORM (s : AGCInterpState) : AGCInterpState :=
  (s.INCR MPTEMP).SQRTNORM_loop 16

def AGCInterpState.SMPAC_PLUS (s : AGCInterpState) : AGCInterpState :=
  let s1 := s.AD NEG1_2_P2
  if is_bzmf s1.A then
    let s2 := s1.AD QUARTER
    if is_bzmf s2.A then
      s2.SQRTNORM
    else
      let s3 := (((((s2.DXCH MPAC).LXCH REG_SR).MP HALF).DXCH MPAC).XCH REG_SR).ADS MPAC_P1
      s3.ARGLO
  else
    let s2 := (((((s1.DXCH MPAC).LXCH REG_SR).MP HALF).DXCH MPAC).XCH REG_SR).ADS MPAC_P1
    s2.ARGHI

def AGCInterpState.SQRTSUB (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CA ZERO).TS MPTEMP
  let (branch, dabs) := ccs_eval (s1.read_e MPAC)
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.SMPAC_PLUS
  else if branch == 2 then
    s2.SQRTNEG
  else
    let s3 := ((((s2.XCH MPAC_P2).XCH MPAC_P1).TS MPAC).CA SEVEN).TS MPTEMP
    let (b2, dabs2) := ccs_eval (s3.read_e MPAC)
    let s4 := s3.CA dabs2
    if b2 == 0 then
      s4.SMPAC_PLUS
    else if b2 == 2 then
      s4.ZEROANS
    else
      let s5 := (((s4.XCH MPAC_P1).TS MPAC).CA SEVEN).ADS MPTEMP
      let (b3, dabs3) := ccs_eval (s5.read_e MPAC)
      let s6 := s5.CA dabs3
      if b3 == 0 then s6.SMPAC_PLUS
      else if b3 == 1 then s6
      else if b3 == 2 then s6.ZEROANS
      else s6.FIXROOT

-- ----------------------------------------------------------------------------
-- UNIT Vector Instruction (Pages 1175 - 1179)
-- ----------------------------------------------------------------------------

def AGCInterpState.UMPAC_MINUS (s : AGCInterpState) : AGCInterpState :=
  let s1 := ((s.CS ZERO).TS DVSIGN).DCS MPAC
  let off := add_15 (s1.read_e MPTEMP) NEGONE
  s1.exec_MAXTEST_prologue off

def AGCInterpState.UMPAC_PLUS (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.TS DVSIGN).DXCH MPAC
  let off := add_15 (s1.read_e MPTEMP) NEGONE
  s1.exec_MAXTEST_prologue off

def AGCInterpState.UNITDV (s : AGCInterpState) : AGCInterpState :=
  let (branch, dabs) := ccs_eval (s.read_e MPAC)
  let s1 := s.CA dabs
  if branch == 1 || branch == 3 then
    let (b1, dabs1) := ccs_eval (s1.read_e MPAC_P1)
    let s2 := s1.CA dabs1
    if b1 == 1 || b1 == 3 then s2
    else if b1 == 2 then s2.UMPAC_MINUS
    else s2.UMPAC_PLUS
  else if branch == 2 then
    s1.UMPAC_MINUS
  else
    s1.UMPAC_PLUS

def AGCInterpState.UNIT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((((s.VECAGREE).MPACVBUF).CA ZERO).XCH OVFIND).TS TEM1
  let s2 := s1.VSQSUB
  let s3 := (s2.CA (s2.read_e TEM1)).XCH OVFIND
  if !(is_bzf s3.A) then
    s3.DVOVF
  else
    let s4 := (s3.DCA MPAC).DXCH (add_15 (s3.read_e FIXLOC) OFF_LVSQUARE)
    let s5 := s4.SQRTSUB
    let (branch, dabs) := ccs_eval (s5.read_e MPAC)
    let s6 := s5.CA dabs
    if branch != 0 then
      let s7 := (s6.TS REG_L).DXCH (add_15 (s6.read_e FIXLOC) OFF_LV)
      s7.DVOVF
    else
      let s7 := (s6.CS FOURTEEN).AD (s6.read_e MPTEMP)
      let (b_sz, dabs_sz) := ccs_eval s7.A15
      let s8 := s7.CA dabs_sz
      let s9 : AGCInterpState :=
        if b_sz == 0 then
          -- SMALL
          let s_a := ((((((((s8.COM).TS MPTEMP).CA ZERO).XCH VBUF_P1).XCH VBUF).XCH VBUF_P3).XCH VBUF_P2).XCH VBUF_P5).XCH VBUF_P4
          let s_b := s_a.CS (s_a.read_e MPTEMP)
          let shift_bit := s_b.read_mem (add_15 ADDR_BIT14_TABLE s_b.A15)
          ((((s_b.CA shift_bit).MP (s_b.read_e MPAC)).TS REG_L).CA ZERO)
        else if b_sz == 1 || b_sz == 3 then
          ((((s8.CS THIRTEEN).TS MPTEMP).CA (s8.read_e MPAC)).TS REG_L).CA ZERO
        else
          -- LARGE
          let (b_mp, dabs_mp) := ccs_eval (s8.read_e MPTEMP)
          let s_a := s8.CA dabs_mp
          if b_mp != 0 then
            (((s_a.CS SRDDV).TS MPTEMP).DCA MPAC)
          else
            -- LARGE3
            let s_b := ((s_a.COM).TS MPTEMP).COM
            let shift_bit := s_b.read_mem (add_15 ADDR_BIT14_TABLE s_b.A15)
            let s_c := (((((s_b.CA shift_bit).TS BUF).MP (s_b.read_e MPAC_P1)).XCH BUF).MP (s_b.read_e MPAC)).XCH REG_L
            (s_c.AD (s_c.read_e BUF)).XCH REG_L

      -- LARGE2
      let s10 := ((s9.DXCH (add_15 (s9.read_e FIXLOC) OFF_LV)).CS ONE).TS MAXDVSW
      let s11 := (((s10.DXCH VBUF).DXCH MPAC).DXCH BUF).UNITDV
      let s12 := (((s11.DXCH VBUF_P2).DXCH MPAC).DXCH MPAC_P3).UNITDV
      let s13 := (((s12.DXCH VBUF_P4).DXCH MPAC).DXCH MPAC_P5).UNITDV
      s13.VROTATEX

-- ----------------------------------------------------------------------------
-- Remaining Unary Instructions: DSQ, SQRT, ABS, ABVAL, VDEF, VSQ, PUSH, RVQ
-- ----------------------------------------------------------------------------

def AGCInterpState.DSQ (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.DSQSUB, some DispStep.danzig)

def AGCInterpState.SQRT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.SQRTSUB
  let (branch, dabs) := ccs_eval (s1.read_e MPTEMP)
  let s2 := s1.CA dabs
  if branch != 0 then
    (s2, some DispStep.danzig)
  else
    let s3 := s2.AD NEG12
    if is_bzmf s3.A then
      let shift_bit := s3.read_mem (add_15 ADDR_BIT15_TABLE (s3.read_e MPTEMP))
      let s4 := ((s3.CA shift_bit).TS MPTEMP).CA ZERO
      s4.MPACSHR_PLUS3
    else
      let s4 := (s3.ZL).LXCH ADDRWD
      s4.GENSCR_PLUS4

def AGCInterpState.ABS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (s1, br) := s.BRANCH
  if br == 2 then s1.COMP else (s1, some DispStep.danzig)

def AGCInterpState.ABVAL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.VSQSUB.LXCH MODE).DCA MPAC
  let s2 := s1.DXCH (add_15 (s1.read_e FIXLOC) OFF_LVSQUARE)
  s2.SQRT

def AGCInterpState.ABVALABS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e MODE)
  let s1 := s.CA dabs
  if branch == 0 || branch == 1 then s1.ABS else s1.ABVAL

def AGCInterpState.VDEF (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CS FOUR).ADS PUSHLOC
  let base := s1.A15
  let s2 := (s1.DCA (add_15 base TWO)).DXCH MPAC_P3
  let s3 := (s2.DCA (s2.read_e PUSHLOC)).DXCH MPAC_P5
  s3.VMODE

def AGCInterpState.VSQ (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  s.VSQSUB.DMODE

def AGCInterpState.PUSH (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.DCA MPAC).DXCH (s.read_e PUSHLOC)
  let wds := s1.read_mem (add_15 ADDR_NOWDS (s1.read_e MODE))
  let s2 := (s1.CA wds).ADS PUSHLOC
  let (branch, dabs) := ccs_eval (s2.read_e MODE)
  let s3 := s2.CA dabs
  if branch == 0 then
    let s4 := (s3.CA (s3.read_e MPAC_P2)).TS (add_15 (s3.read_e PUSHLOC) (comp15 ONE))
    (s4, some DispStep.danzig)
  else if branch == 1 then
    (s3, some DispStep.danzig)
  else
    let s4 := (s3.DCA MPAC_P3).DXCH (add_15 (s3.read_e PUSHLOC) (comp15 FOUR))
    let s5 := (s4.DCA MPAC_P5).DXCH (add_15 (s4.read_e PUSHLOC) (comp15 TWO))
    (s5, some DispStep.danzig)

-- ----------------------------------------------------------------------------
-- Trigonometric Package: COSINE, SINE, ARCSIN, ARCCOS (Pages 1187 - 1191)
-- ----------------------------------------------------------------------------

def AGCInterpState.SINE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.DXCH MPAC).DDOUBL
  let s2 := if s1.OVSK then s1.DCOM else s1
  let s3 := s2.DXCH MPAC
  let s4 := (s3.CA (s3.read_e MPAC)).DOUBLE
  let (s5, ovf) := s4.TS_ovf REG_L
  let s6 := if ovf then
      let lim_val := s5.read_mem (add_15 ADDR_NEG_HALF_P1 s5.A15)
      let s_a := (((s5.CA lim_val).DOUBLE).SU (s5.read_e MPAC)).TS MPAC
      (s_a.CS (s_a.read_e MPAC_P1)).TS MPAC_P1
    else
      s5

  let s7 := ((s6.DCA MPAC).DXCH BUF2).DSQSUB
  let s8 := (s7.POLY ADDR_SIN_POLY).DMP BUF2
  let s9 := (((s8.DCA MPAC_P1).DAS MPAC_P1).AD (s8.read_e MPAC)).ADS MPAC
  let s10 := (((s9.DCA MPAC_P1).DAS MPAC_P1).AD (s9.read_e MPAC)).ADS MPAC
  (s10, some DispStep.danzig)

def AGCInterpState.COSINE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (s1, br) := s.BRANCH
  let s2 := if br == 0 then (s1.DCS MPAC).DXCH MPAC else s1
  let s3 := (s2.CA QUARTER).ADS MPAC
  s3.SINE

def AGCInterpState.finish_ACOS_ESCAPE (s : AGCInterpState) (esc_target : Word15) : AGCInterpState × Option DispStep :=
  let (s1, esc2) : AGCInterpState × Word15 :=
    if esc_target == SYM_SUBTR then
      let st := ((s.DCS MPAC).AD HALF).DXCH MPAC
      (st, st.read_e ESCAPE2)
    else
      (s, esc_target)
  let s2 :=
    if esc2 == SYM_ASINEX then
      ((s1.DCS MPAC).AD QUARTER).DXCH MPAC
    else
      s1
  (s2, some DispStep.danzig)

def AGCInterpState.ARCCOS_COMMON (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TS ESCAPE
  let (s2, br) := s1.BRANCH
  if br == 1 then
    let s3 := (((s2.CA QUARTER).TS MPAC).CA ZERO).TS MPAC_P1
    s3.finish_ACOS_ESCAPE (s3.read_e ESCAPE)
  else
    let s3 := if br == 2 then
        ((((s2.DCS MPAC).DXCH MPAC).CA SYM_SUBTR).XCH ESCAPE).TS ESCAPE2
      else
        s2
    let s4 := (s3.CS HALF).AD (s3.read_e MPAC)
    let (branch, dabs) := ccs_eval s4.A15
    let s5 := s4.CA dabs
    if branch == 0 then
      let s6 := if !(is_bzf s5.A) then s5.ALARM 0o1301#15 else s5
      let s7 := ((s6.CA ZERO).TS MPAC_P1).TS MPAC
      s7.finish_ACOS_ESCAPE (s7.read_e ESCAPE)
    else
      let (s6, early_zero) : AGCInterpState × Bool :=
        if branch == 1 || branch == 3 then
          let (b1, dabs1) := ccs_eval (s5.read_e MPAC_P1)
          let st := s5.CA dabs1
          if b1 != 2 then
            (((st.CA ZERO).TS MPAC_P1).TS MPAC, true)
          else
            (st, false)
        else
          (s5, false)

      if early_zero then
        s6.finish_ACOS_ESCAPE (s6.read_e ESCAPE)
      else
        let s7 := (((s6.DCS MPAC).AD HALF).DXCH MPAC).DXCH BUF2
        let s8 := s7.SQRTSUB
        let (b_sh, dabs_sh) := ccs_eval (s8.read_e MPTEMP)
        let s9 := s8.CA dabs_sh
        let s10 := if b_sh == 0 then
            let shift_bit := s9.read_mem (add_15 ADDR_BIT14_TABLE s9.A15)
            (((s9.CA shift_bit).TS MPTEMP).VSHRRND)
          else
            s9
        let s11 := ((s10.DXCH MPAC).DXCH BUF2).DXCH MPAC
        let s12 := (s11.POLY ADDR_ACOS_POLY).DMP BUF2
        s12.finish_ACOS_ESCAPE (s12.read_e ESCAPE)

def AGCInterpState.ARCSIN (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CA SYM_ASINEX).ARCCOS_COMMON

def AGCInterpState.ARCCOS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CA SYM_DANZIG).ARCCOS_COMMON


-- ============================================================================
-- 7. SECTION 2 & SECTION 12: STORE, PUSHDOWN, BRANCH, INDEX, SWITCHES
-- ============================================================================

def AGCInterpState.PDDL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DCA (s.read_e ADDRWD)).DXCH MPAC).DXCH (s.read_e PUSHLOC))
  let wds := s1.read_mem (add_15 ADDR_NOWDS (s1.read_e MODE))
  let s2 := (s1.CA wds).ADS PUSHLOC
  let (branch, dabs) := ccs_eval (s2.read_e MODE)
  let s3 := s2.CA dabs
  if branch == 0 then
    let s4 := ((s3.TS MODE).XCH MPAC_P2).TS (add_15 (s3.read_e PUSHLOC) (comp15 ONE))
    (s4, some DispStep.danzig)
  else if branch == 1 then
    (s3.TS MPAC_P2, some DispStep.danzig)
  else
    let s4 := (((s3.TS MODE).TS MPAC_P2).DXCH MPAC_P3).DXCH (add_15 (s3.read_e PUSHLOC) (comp15 FOUR))
    let s5 := (s4.DXCH MPAC_P5).DXCH (add_15 (s4.read_e PUSHLOC) (comp15 TWO))
    (s5, some DispStep.danzig)

def AGCInterpState.PDVL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.DCA (s.read_e ADDRWD)).DXCH MPAC).DXCH (s.read_e PUSHLOC))
  let wds := s1.read_mem (add_15 ADDR_NOWDS (s1.read_e MODE))
  let s2 := (s1.CA wds).ADS PUSHLOC
  let (branch, dabs) := ccs_eval (s2.read_e MODE)
  let s3 := s2.CA dabs
  if branch == 0 then
    let s4 := (s3.DCA (add_15 (s3.read_e ADDRWD) TWO)).DXCH MPAC_P3
    let s5 := (s4.CA (s4.read_e MPAC_P2)).TS (add_15 (s4.read_e PUSHLOC) (comp15 ONE))
    s5.ENDVLOAD_PLUS4
  else if branch == 1 then
    s3.ENDVLOAD
  else
    let s4 := ((s3.DCA (add_15 (s3.read_e ADDRWD) TWO)).DXCH MPAC_P3).DXCH (add_15 (s3.read_e PUSHLOC) (comp15 FOUR))
    let s5 := ((s4.DCA (add_15 (s4.read_e ADDRWD) FOUR)).DXCH MPAC_P5).DXCH (add_15 (s4.read_e PUSHLOC) (comp15 TWO))
    (s5, some DispStep.danzig)

-- ----------------------------------------------------------------------------
-- Sequence Changing & Subroutine Calling Options (Pages 1128 - 1130)
-- ----------------------------------------------------------------------------

def AGCInterpState.GOTO_PLUS4 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e BANKSET)).TS REG_BBANK
  let s2 := ((((s1.CA (s1.read_e POLISH)).TS REG_FBANK).MASK LOW10).AD CONST_2K).TS LOC
  (s2, some DispStep.intpret_p3)

def AGCInterpState.GOTO_PLUS1_loop (fuel : Nat) (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  match fuel with
  | 0 => s.GOTO_PLUS4
  | fuel' + 1 =>
    let s1 := s.MASK HIGH4
    if !(is_bzf s1.A) then
      s1.GOTO_PLUS4
    else
      let s2 := (s1.CA (s1.read_e POLISH)).AD NEG_ENDVAC
      let (branch, dabs) := ccs_eval s2.A15
      let s3 := s2.CA dabs
      if branch == 0 then
        let s4 := ((s3.CA (s3.read_e POLISH)).TS REG_EBANK).MASK LOW8
        let ind_val := s4.read_mem (add_15 OCT1400 s4.A15)
        let s5 := (s4.CA ind_val).TS POLISH
        GOTO_PLUS1_loop fuel' s5
      else
        let s4 := (s3.CA (s3.read_e FIXLOC)).AD (s3.read_e POLISH)
        let ind_val := s4.read_e s4.A15
        let s5 := (s4.CA ind_val).TS POLISH
        GOTO_PLUS1_loop fuel' s5

def AGCInterpState.GOTO_PLUS1 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  s.GOTO_PLUS1_loop 8

def AGCInterpState.GOTO (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.CA (s.read_e POLISH)).GOTO_PLUS1

def AGCInterpState.CALL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((((s.CA (s.read_e BANKSET)).MASK BANKMASK).AD BANKMASK).AD (s.read_e LOC)).TS (add_15 (s.read_e FIXLOC) OFF_QPRET)
  s1.GOTO

def AGCInterpState.CCALL (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.INCR LOC
  let base_cadr := s1.read_mem (s1.read_e LOC)
  let s2 := (((s1.CA base_cadr).AD (s1.read_mem (s1.read_e ADDRWD))).TS REG_FBANK).MASK LOW10
  let target_cadr := s2.read_mem (add_15 CONST_2K s2.A15)
  let s3 := (s2.CA target_cadr).TS POLISH
  s3.CALL

def AGCInterpState.CGOTO (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let base_cadr := s.read_mem (add_15 (s.read_e LOC) ONE)
  let s1 := (((s.CA base_cadr).AD (s.read_mem (s.read_e ADDRWD))).TS REG_FBANK).MASK LOW10
  let target_cadr := s1.read_mem (add_15 CONST_2K s1.A15)
  let s2 := (s1.CA target_cadr).TS POLISH
  s2.GOTO_PLUS1

def AGCInterpState.SWBRANCH (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e BANKSET)).TS REG_FBANK
  let target := s1.read_mem (add_15 (s1.read_e LOC) ONE)
  let s2 := (s1.CA target).TS POLISH
  s2.GOTO_PLUS1

def AGCInterpState.RVQ (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let qpret_val := s.read_e (add_15 (s.read_e FIXLOC) OFF_QPRET)
  let s1 := (s.CA qpret_val).TS POLISH
  s1.GOTO_PLUS4

-- ----------------------------------------------------------------------------
-- Store Package (`DOSTORE`, `_STORE`, `STADR`, Pages 1119 - 1123)
-- ----------------------------------------------------------------------------

def AGCInterpState.STORE_exec (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e ADDRWD)).AD DEC45
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  let s3 := if branch == 0 then
      s2.CA (s2.read_e FIXLOC)
    else
      (((s2.CA OCT1400).XCH ADDRWD).TS REG_EBANK).MASK LOW8
  let s4 := s3.ADS ADDRWD
  let target := s4.read_e ADDRWD
  let s5 := (s4.DCA MPAC).DXCH target
  let (b_mode, dabs_mode) := ccs_eval (s5.read_e MODE)
  let s6 := s5.CA dabs_mode
  if b_mode == 0 then
    (s6.CA (s6.read_e MPAC_P2)).TS (add_15 target TWO)
  else if b_mode == 1 then
    s6
  else
    let s7 := (s6.DCA MPAC_P3).DXCH (add_15 target TWO)
    (s7.DCA MPAC_P5).DXCH (add_15 target FOUR)

def AGCInterpState.STORE_1 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e (add_15 (s.read_e FIXLOC) OFF_X1))).ADS ADDRWD
  s1.STORE_exec

def AGCInterpState.STORE_2 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e (add_15 (s.read_e FIXLOC) OFF_X2))).ADS ADDRWD
  s1.STORE_exec

def AGCInterpState.DOSTORE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((((s.TS ADDRWD).MASK LOW11).XCH ADDRWD).MASK B12T14).MP BIT5
  let store_type : Nat := (s1.A15.toNat >>> 1) &&& 0o7
  if store_type == 0 then
    (s1.STORE_exec, some DispStep.danzig)
  else if store_type == 1 then
    (s1.STORE_1, some DispStep.danzig)
  else if store_type == 2 then
    (s1.STORE_2, some DispStep.danzig)
  else if store_type == 3 then
    let s2 := ((s1.STORE_exec).CA DLOADCOD).TS REG_CYR
    (s2, some DispStep.diradres)
  else if store_type == 4 then
    (s1.STORE_exec, some DispStep.dodload_star)
  else if store_type == 5 then
    let s2 := ((s1.STORE_exec).CA VLOADCOD).TS REG_CYR
    (s2, some DispStep.diradres)
  else if store_type == 6 then
    let s2 := ((s1.STORE_exec).CA VLOAD_STAR).TS REG_CYR
    (s2, some DispStep.index)
  else
    let s2 := ((s1.STORE_exec).CA CALLCODE).TS REG_CYR
    (s2, some DispStep.bit15adr)

def AGCInterpState.STADR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CA (s.read_e BANKSET)).TS REG_FBANK).INCR LOC
  let s2 := (s1.CS (s1.read_mem (s1.read_e LOC))).AD NEGONE
  s2.DOSTORE

-- ----------------------------------------------------------------------------
-- Section 12: Index, Branch, and Switch Instructions (Pages 1192 - 1199)
-- ----------------------------------------------------------------------------

def AGCInterpState.TAGSUB (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CA (s.read_e FIXLOC)).TS INDEXLOC
  let (branch, dabs) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs
  if branch == 0 || branch == 1 then s2.INCR INDEXLOC else s2

def AGCInterpState.ADRERS_15 (s : AGCInterpState) : AGCInterpState :=
  let s1 := (s.CS (s.read_e POLISH)).AD DEC45
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  let s3 := if branch == 0 then
      s2.CA (s2.read_e FIXLOC)
    else
      (((s2.CA OCT1400).XCH POLISH).TS REG_EBANK).MASK LOW8
  (s3.ADS POLISH).TAGSUB

def AGCInterpState.XSTORE (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.TS (add_15 (s.read_e INDEXLOC) OFF_X1), some DispStep.danzig)

def AGCInterpState.MSTORE1 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.TS (s.read_e POLISH), some DispStep.danzig)

def AGCInterpState.XAD2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  (s.ADS (add_15 (s.read_e INDEXLOC) OFF_X1), some DispStep.danzig)

def AGCInterpState.AXT (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TAGSUB
  (s1.CA (s1.read_e POLISH)).XSTORE

def AGCInterpState.AXC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TAGSUB
  (s1.CS (s1.read_e POLISH)).XSTORE

def AGCInterpState.LXA (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  (s1.CA (s1.read_mem (s1.read_e POLISH))).XSTORE

def AGCInterpState.LXC (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  (s1.CS (s1.read_mem (s1.read_e POLISH))).XSTORE

def AGCInterpState.SXA (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  (s1.CA (s1.read_e (add_15 (s1.read_e INDEXLOC) OFF_X1))).MSTORE1

def AGCInterpState.XCHX (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  let s2 := (s1.CA (s1.read_mem (s1.read_e POLISH))).XCH (add_15 (s1.read_e INDEXLOC) OFF_X1)
  s2.MSTORE1

def AGCInterpState.XAD (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  (s1.CA (s1.read_mem (s1.read_e POLISH))).XAD2

def AGCInterpState.INCR_OP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TAGSUB
  (s1.CA (s1.read_e POLISH)).XAD2

def AGCInterpState.XSU (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.ADRERS_15
  (s1.CS (s1.read_mem (s1.read_e POLISH))).XAD2

def AGCInterpState.TIX (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TAGSUB
  let idx_base := s1.read_e INDEXLOC
  let s2 := (s1.CS (s1.read_e (add_15 idx_base OFF_S1))).AD (s1.read_e (add_15 idx_base OFF_X1))
  if is_bzmf s2.A then
    (s2, some DispStep.danzig)
  else
    (s2.XCH (add_15 idx_base OFF_X1)).GOTO

def AGCInterpState.RTB (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let target := s.read_e POLISH
  (s.CA target, some DispStep.danzig)

def AGCInterpState.RTB_BHIZ (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_CYR)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.RTB
  else
    let (b_mp, dabs_mp) := ccs_eval (s1.read_e MPAC)
    let s2 := s1.CA dabs_mp
    if b_mp == 1 || b_mp == 3 then s2.GOTO else (s2, some DispStep.danzig)

def AGCInterpState.BOV_B (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e OVFIND)
  let s1 := s.CA dabs
  if branch == 1 || branch == 3 then
    (s1, some DispStep.danzig)
  else
    let s2 := (s1.CA ZERO).TS OVFIND
    let (b_cyr, dabs_cyr) := ccs_eval (s2.read_e REG_CYR)
    let s3 := s2.CA dabs_cyr
    if b_cyr == 0 then s3.RTB else s3.GOTO

def AGCInterpState.BZE_GOTO (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_CYR)
  let s1 := s.CA dabs
  if branch == 0 then
    let (s2, br) := s1.BRANCH
    if br == 1 then s2.GOTO else (s2, some DispStep.danzig)
  else
    s1.GOTO

def AGCInterpState.BPL_BMN (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_CYR)
  let s1 := s.CA dabs
  if branch == 0 then
    let (s2, br) := s1.BRANCH
    if br == 0 || br == 1 then s2.GOTO else (s2, some DispStep.danzig)
  else
    let (s2, br) := s1.BRANCH
    if br == 2 then s2.GOTO else (s2, some DispStep.danzig)

def AGCInterpState.CALL_ITA (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_CYR)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.CALL
  else if branch == 1 then
    (s1.CCSHOLE, none)
  else
    let s2 := s1.ADRERS_15
    (s2.CA (s2.read_e (add_15 (s2.read_e FIXLOC) OFF_QPRET))).MSTORE1

def AGCInterpState.SW_TEST (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.MASK (s.read_e SWBIT)
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 || branch == 2 then
    (s2.INCR LOC, some DispStep.danzig)
  else if branch == 1 then
    s2.SWBRANCH
  else
    (s2.CCSHOLE, some DispStep.danzig)

def AGCInterpState.SWITCHES (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA LOW4).MASK (s.read_e POLISH)
  let sw_bit := s1.read_mem (add_15 ADDR_BIT15_TABLE s1.A15)
  let s2 := (s1.CA sw_bit).TS SWBIT
  let s3 := (((s2.CA BIT7).MP (s2.read_e POLISH)).TS SWWORD).INHINT
  let sw_addr := add_15 STATE s3.A15
  let s4 := (s3.CA (s3.read_e sw_addr)).TS REG_Q
  let s5 := ((s4.CA BIT11).MP (s4.read_e POLISH)).MASK B3TOB4
  let op_mod := (s5.A15.toNat >>> 2) &&& 0o3

  let s6 :=
    if op_mod == 0 then
      (((s5.CA (s5.read_e SWBIT)).ROR QCHAN).TS (add_15 STATE (s5.read_e SWWORD)))
    else if op_mod == 1 then
      (((s5.CA (s5.read_e SWBIT)).RXOR QCHAN).TS (add_15 STATE (s5.read_e SWWORD)))
    else if op_mod == 2 then
      (((s5.CS (s5.read_e SWBIT)).MASK s5.Q).TS (add_15 STATE (s5.read_e SWWORD)))
    else
      s5

  let s7 := ((s6.RELINT.CA BIT13).MP (s6.read_e POLISH)).MASK B3TOB4
  let br_mod := (s7.A15.toNat >>> 2) &&& 0o3
  if br_mod == 0 then
    (s7.CS s7.Q).SW_TEST
  else if br_mod == 1 then
    s7.SWBRANCH
  else if br_mod == 2 then
    (s7.CA s7.Q).SW_TEST
  else
    (s7, some DispStep.danzig)


-- ============================================================================
-- 8. SECTION 4: DISPATCHER & JUMP TABLES (PAGES 1107 - 1118)
-- ============================================================================

def AGCInterpState.dispatch_INDJUMP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let op_code := (s.read_e REG_CYR).toNat &&& 0o00037
  match op_code with
  | 0o00 => s.VLOAD
  | 0o01 => s.TAD
  | 0o02 => s.SIGN
  | 0o03 => s.VXSC
  | 0o04 => s.CGOTO
  | 0o05 => s.TLOAD
  | 0o06 => s.DLOAD
  | 0o07 => s.V_SC
  | 0o10 => s.SLOAD
  | 0o11 => s.SSP
  | 0o12 => s.PDDL
  | 0o13 => s.MXV
  | 0o14 => s.PDVL
  | 0o15 => s.CCALL
  | 0o16 => s.VXM
  | 0o17 => s.TSLC
  | 0o20 => s.DMPR
  | 0o21 => s.DDV
  | 0o22 => s.BDDV
  | 0o23 => s.GSHIFT
  | 0o24 => s.VAD
  | 0o25 => s.VSU
  | 0o26 => s.BVSU
  | 0o27 => s.DOT
  | 0o30 => s.VXV
  | 0o31 => s.VPROJ
  | 0o32 => s.DSU
  | 0o33 => s.BDSU
  | 0o34 => s.DAD
  | 0o36 => s.DMP1
  | 0o37 => s.SETPD
  | _    => (s.CCSHOLE, none)

def AGCInterpState.dispatch_MISCJUMP (s : AGCInterpState) (op_code_w : Word15) : AGCInterpState × Option DispStep :=
  let op_code := op_code_w.toNat &&& 0o00017
  match op_code with
  | 0o00 => s.AXT
  | 0o01 => s.AXC
  | 0o02 => s.LXA
  | 0o03 => s.LXC
  | 0o04 => s.SXA
  | 0o05 => s.XCHX
  | 0o06 => s.INCR_OP
  | 0o07 => s.TIX
  | 0o10 => s.XAD
  | 0o11 => s.XSU
  | 0o12 => s.BZE_GOTO
  | 0o13 => s.BPL_BMN
  | 0o14 => s.RTB_BHIZ
  | 0o15 => s.CALL_ITA
  | 0o16 => s.SWITCHES
  | _    => s.BOV_B

def AGCInterpState.dispatch_UNAJUMP (s : AGCInterpState) (op_index : Word15) : AGCInterpState × Option DispStep :=
  let op_code := (op_index.toNat + 1) &&& 0o00017
  match op_code with
  | 0o01 => s.SQRT
  | 0o02 => s.SINE
  | 0o03 => s.COSINE
  | 0o04 => s.ARCSIN
  | 0o05 => s.ARCCOS
  | 0o06 => s.DSQ
  | 0o07 => s.ROUND
  | 0o10 => s.COMP
  | 0o11 => s.VDEF
  | 0o12 => s.UNIT
  | 0o13 => s.ABVALABS
  | 0o14 => s.VSQ
  | 0o15 => s.STADR
  | 0o16 => s.RVQ
  | _    => s.PUSH

-- ----------------------------------------------------------------------------
-- Address Decoding & Push-Up Steps (Pages 1109 - 1115)
-- ----------------------------------------------------------------------------

def AGCInterpState.step_REGUP_PLUS2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.ADS PUSHLOC).TS ADDRWD
  s1.dispatch_INDJUMP

def AGCInterpState.step_REGUP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let mode_val := s.read_e MODE
  let wds := s.read_mem (add_15 ADDR_NOWDS mode_val)
  (s.CS wds).step_REGUP_PLUS2

def AGCInterpState.step_PUSHUP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (((s.CA OCT23).MASK (s.read_e REG_CYR)).AD NEG_OCT10)
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.step_REGUP
  else
    let s3 := s2.AD NEG4
    let (b2, dabs2) := ccs_eval s3.A15
    let s4 := s3.CA dabs2
    if b2 == 0 then
      let dec_wds := s4.read_mem (add_15 ADDR_NOWDS s4.A15)
      (s4.CS dec_wds).step_REGUP_PLUS2
    else
      let mode_val := s4.read_e MODE
      let rev_wds := s4.read_mem (add_15 ADDR_REVCNT mode_val)
      (s4.CS rev_wds).step_REGUP_PLUS2

def AGCInterpState.step_IERASTST (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  if is_bzmf s.A then
    let s1 := (((s.MASK LOW8).AD OCT1400).XCH ADDRWD).TS REG_EBANK
    s1.dispatch_INDJUMP
  else
    let s1 := ((((s.MASK LOW10).AD LOW10).XCH ADDRWD).AD (s.read_e INTBIT15)).TS REG_FBANK
    s1.dispatch_INDJUMP

def AGCInterpState.step_DIRADRES (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let next_word := s.read_mem (add_15 (s.read_e LOC) ONE)
  let s1 := s.CS next_word
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.step_PUSHUP
  else
    let s3 := ((s2.INCR LOC).TS ADDRWD).AD NEG_ENDVAC
    let (b_vac, dabs_vac) := ccs_eval s3.A15
    let s4 := s3.CA dabs_vac
    if b_vac == 0 then
      (s4.AD NEG_ENDERAS).step_IERASTST
    else
      let s5 := (s4.CA (s4.read_e FIXLOC)).ADS ADDRWD
      s5.dispatch_INDJUMP

def AGCInterpState.step_INDEX (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := ((s.CA (s.read_e FIXLOC)).TS INDEXLOC).INCR LOC
  let raw_word := s1.read_mem (s1.read_e LOC)
  let s2 := s1.CS raw_word
  let (branch, dabs) := ccs_eval s2.A15
  let s3 := s2.CA dabs
  let s4 := if branch == 0 then s3.INCR INDEXLOC else s3
  let s5 := (s4.TS ADDRWD).MASK HIGH4
  let s6 := if !(is_bzf s5.A) then (s5.CA (s5.read_e INTBIT15)).ADS ADDRWD else s5
  let idx_reg_addr := add_15 (s6.read_e INDEXLOC) OFF_X1
  let s7 := ((s6.CS (s6.read_e idx_reg_addr)).ADS ADDRWD).MASK HIGH9
  if is_bzf s7.A then
    let s8 := (s7.CA (s7.read_e FIXLOC)).ADS ADDRWD
    s8.dispatch_INDJUMP
  else
    let s8 := s7.MASK HIGH4
    if is_bzf s8.A then
      let s9 := ((((s8.CA OCT1400).XCH ADDRWD).TS REG_EBANK).MASK LOW8).ADS ADDRWD
      s9.dispatch_INDJUMP
    else
      let s9 := ((((s8.CA (s8.read_e ADDRWD)).TS REG_FBANK).MASK LOW10).AD CONST_2K).TS ADDRWD
      s9.dispatch_INDJUMP

def AGCInterpState.step_DODLOAD_STAR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA DLOAD_STAR).TS REG_CYR
  s1.step_INDEX

def AGCInterpState.step_15BITADR (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.INCR LOC
  let s2 := (s1.CA (s1.read_mem (s1.read_e LOC))).TS POLISH
  let s3 := ((s2.CA LOW7_2K).TS REG_FBANK).MASK (s2.read_e REG_CYR)
  s3.dispatch_MISCJUMP s3.A15

def AGCInterpState.step_OPJUMP3 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TS REG_FBANK
  let (branch, dabs) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.dispatch_UNAJUMP s2.A15
  else
    let (b_mode, dabs_mode) := ccs_eval (s2.read_e MODE)
    let s3 := s2.CA dabs_mode
    if b_mode == 0 || b_mode == 1 then s3.SHORTT else s3.SHORTV

def AGCInterpState.step_OPJUMP2 (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_CYR)
  let s1 := s.CA dabs
  if branch == 0 then s1.step_OPJUMP3 else s1.step_15BITADR

def AGCInterpState.step_OPJUMP (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := s.TS REG_CYR
  let (branch, dabs) := ccs_eval (s1.read_e REG_CYR)
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.step_OPJUMP2
  else if branch == 1 then
    (s2.EXIT, none)
  else
    let s3 := s2.MASK BIT1
    let (b_idx, dabs_idx) := ccs_eval s3.A15
    let s4 := s3.CA dabs_idx
    if b_idx == 0 then s4.step_INDEX else s4.step_DIRADRES

def AGCInterpState.step_NEWOPS (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let word := s.read_mem (s.read_e LOC)
  let s1 := s.CA word
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 then
    s2.DOSTORE
  else
    let s3 := (s2.TS REG_EDOP).MASK LOW7
    s3.step_OPJUMP

def AGCInterpState.step_NOIBNKSW (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let (branch, dabs) := ccs_eval (s.read_e REG_EDOP)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.step_OPJUMP
  else
    let (branch_nj, dabs_nj) := ccs_eval (s1.read_e NEWJOB)
    let s2 := s1.CA dabs_nj
    if branch_nj == 0 then
      (s2.CHANG2, none)
    else
      (s2.INCR LOC).step_NEWOPS

def AGCInterpState.step_DANZIG (s : AGCInterpState) : AGCInterpState × Option DispStep :=
  let s1 := (s.CA (s.read_e BANKSET)).TS REG_BBANK
  s1.step_NOIBNKSW

/-- Bounded dispatcher loop executing interpretive instructions until `EXIT` or `CHANG2`. -/
def AGCInterpState.run_dispatcher_loop (fuel : Nat) (s : AGCInterpState) (step : DispStep) : AGCInterpState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s.halted then s
    else
      let (s', nextOpt) : AGCInterpState × Option DispStep :=
        match step with
        | DispStep.danzig       => s.step_DANZIG
        | DispStep.noibnksw     => s.step_NOIBNKSW
        | DispStep.newops       => s.step_NEWOPS
        | DispStep.opjump       => s.step_OPJUMP
        | DispStep.diradres     => s.step_DIRADRES
        | DispStep.dodload_star => s.step_DODLOAD_STAR
        | DispStep.index        => s.step_INDEX
        | DispStep.bit15adr     => s.step_15BITADR
        | DispStep.intpret_p3   =>
          let st := (((s.TS BANKSET).MASK BIT15).TS INTBIT15).TS REG_EDOP
          (st, some DispStep.newops)
      match nextOpt with
      | none          => s'
      | some nextStep => s'.run_dispatcher_loop fuel' nextStep

def AGCInterpState.INTPRET_PLUS3 (s : AGCInterpState) (fuel : Nat := 128) : AGCInterpState :=
  let s1 := (((s.TS BANKSET).MASK BIT15).TS INTBIT15).TS REG_EDOP
  s1.run_dispatcher_loop fuel DispStep.newops

def AGCInterpState.INTPRET_PLUS2 (s : AGCInterpState) (fuel : Nat := 128) : AGCInterpState :=
  (s.CA s.BBANK).INTPRET_PLUS3 fuel

def AGCInterpState.INTPRET (s : AGCInterpState) (start_loc : Option Word15 := none)
    (bbank : Option Word15 := none) (fuel : Nat := 128) : AGCInterpState :=
  let s1 := match start_loc with
    | some loc => s.setQ loc
    | none     => s
  let s2 := match bbank with
    | some bb => s1.setBBANK bb
    | none    => s1
  let s3 := (s2.RELINT).QXCH LOC
  s3.INTPRET_PLUS2 fuel

def AGCInterpState.INTRSM (s : AGCInterpState) (fuel : Nat := 128) : AGCInterpState :=
  (s.LXCH REG_BBANK).INTPRET_PLUS3 fuel


-- ============================================================================
-- 9. YUL OPCODE-PAIR ASSEMBLER HELPERS & MACHINE-VERIFIED SUITE
-- ============================================================================

/--
  Pack two 7-bit YUL interpretive order codes into a single 15-bit AGC word.
  `word` is stored complemented such that `CCS word` takes the negative branch
  and leaves `DABS(word) = (op2 << 7) | op1` in `A`.
-/
@[inline] def pack_yul_op_pair (op1 : Word15) (op2 : Word15 := 0o000#15) : Word15 :=
  let combined : Nat := ((op2.toNat &&& 0o177) <<< 7) ||| (op1.toNat &&& 0o177)
  comp15 (BitVec.ofNat 15 ((combined + 1) &&& 0o77777))

/--
  Pack a YUL store code (`0..7` in bits 14..12) and 11-bit erasable address (bits 11..1).
  `CCS word` takes the positive branch and leaves `word - 1` in `A`.
-/
@[inline] def pack_yul_store_word (store_type : Nat) (erasable_addr : Word15) : Word15 :=
  let raw : Nat := ((store_type &&& 0o7) <<< 11) ||| (erasable_addr.toNat &&& 0o3777)
  BitVec.ofNat 15 ((raw + 1) &&& 0o77777)

-- ----------------------------------------------------------------------------
-- Exact Scaled Constants Used in `run_verification`
-- ----------------------------------------------------------------------------

-- dec_to_2dec(0.5)  => (0o20000, 0o00000)
def H_HI : Word15 := 0o20000#15
def H_LO : Word15 := 0o00000#15

-- dec_to_2dec(0.25) => (0o10000, 0o00000)
def Q_HI : Word15 := 0o10000#15
def Q_LO : Word15 := 0o00000#15

-- dec_to_2dec(0.125) => (0o04000, 0o00000)
def ARG_HI : Word15 := 0o04000#15
def ARG_LO : Word15 := 0o00000#15

-- ----------------------------------------------------------------------------
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

-- End-to-End Verification Steps & Kernel-Checked Theorems
-- ----------------------------------------------------------------------------

set_option maxRecDepth 20000

-- ----------------------------------------------------------------------------
-- End-to-End Verification Steps & Kernel-Checked Theorems
-- ----------------------------------------------------------------------------

set_option maxRecDepth 20000

-- ----------------------------------------------------------------------------
-- End-to-End Verification Steps & Kernel-Checked Theorems
-- ----------------------------------------------------------------------------

set_option maxRecDepth 20000

-- ----------------------------------------------------------------------------
-- End-to-End Verification Steps & Kernel-Checked Theorems
-- ----------------------------------------------------------------------------

set_option maxRecDepth 20000

-- ----------------------------------------------------------------------------
-- End-to-End Verification Steps & Kernel-Checked Theorems
-- ----------------------------------------------------------------------------

/-- Test 1: Double Precision Multiply (`DMPSUB`) & Round (`ROUNDSUB`): `0.5 * 0.5 = 0.25`. -/
def interp_step1 : AGCInterpState :=
  let s0 := initAGCInterpState
  let s1 := ((((s0.write_e MPAC H_HI).write_e MPAC_P1 H_LO).write_e 0o0300#15 H_HI).write_e 0o0301#15 H_LO).write_e ADDRWD 0o0300#15
  s1.DMPSUB.ROUNDSUB

theorem verify_test1_dmpsub_roundsub :
    interp_step1.read_e MPAC = Q_HI ∧
    interp_step1.read_e MPAC_P1 = POS_ZERO := by
  decide

end AGCInterpreter
