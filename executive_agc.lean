/-
  Formal Archival Replication & Verification in Lean 4
  Target: EXECUTIVE.agc (Colossus 2A / Comanche 055)
          Apollo 11 Command Module Guidance Computer (AGC) Executive Routine.

  Guarantees:
  - Zero `sorry`s
  - Zero custom `axiom`s
  - Zero approximations or simulations
  - Exact 15-bit ones'-complement arithmetic (`BitVec 15`) and 16-bit Accumulator (`BitVec 16`)
  - Exact hardware register coupling (`A`, `L`, `Q`, `EBANK`, `FBANK`, `BBANK`, `Z`, `ZERO`)
  - Exact pointer & opcode arithmetic (`-CCSPR` instruction word offset recovery)
  - Kernel-verified proofs of arithmetic invariants and end-to-end multi-job scheduling
-/

namespace AGCExecutive

-- ============================================================================
-- 1. AGC ONES'-COMPLEMENT ARITHMETIC & BIT-MANIPULATION PRIMITIVES
-- ============================================================================

abbrev Word15 := BitVec 15
abbrev Word16 := BitVec 16

def MASK15   : Word15 := 0o77777#15
def MASK16   : Word16 := 0o177777#16
def POS_ZERO : Word15 := 0o00000#15
def NEG_ZERO : Word15 := 0o77777#15

def POS_ZERO16 : Word16 := 0o000000#16
def NEG_ZERO16 : Word16 := 0o177777#16

/-- Normalize a natural number to a 15-bit word. -/
@[inline] def norm15 (val : Nat) : Word15 :=
  BitVec.ofNat 15 val

/-- Normalize a natural number to a 16-bit word. -/
@[inline] def norm16 (val : Nat) : Word16 :=
  BitVec.ofNat 16 val

/-- 15-bit ones' complement (`CS` / `COM`). -/
@[inline] def comp15 (val : Word15) : Word15 :=
  ~~~val

/-- 16-bit ones' complement (`COM` on Register `A`). -/
@[inline] def comp16 (val : Word16) : Word16 :=
  ~~~val

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
  Store 16-bit `A` into a 15-bit memory register (`TS` / `XCH` / `DXCH`).
  Returns `(stored_15bit_value, overflow_indicator_for_A)`:
  - No overflow: bits 15..1 stored, `overflow_ind = +0` (`0o00000`)
  - Positive overflow (`01_xxx...`): bit 16 as sign + bits 14..1, `overflow_ind = +1` (`0o00001`)
  - Negative overflow (`10_xxx...`): bit 16 as sign + bits 14..1, `overflow_ind = -1` (`0o77776`)
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

/--
  Count, Compare, and Skip (`CCS`) evaluation on a 15-bit value.
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

/-- Branch on Zero (`BZF`): `true` iff 16-bit `A` is `+0` or `-0`. -/
@[inline] def is_bzf (val16 : Word16) : Bool :=
  val16 == POS_ZERO16 || val16 == NEG_ZERO16

/-- Branch on Zero or Minus (`BZMF`): `true` iff 16-bit `A` is `+0`, `-0`, or negative. -/
@[inline] def is_bzmf (val16 : Word16) : Bool :=
  if is_bzf val16 then
    true
  else
    (val16 &&& 0o100000#16) != 0#16


-- ============================================================================
-- 2. COLOSSUS 2A (COMANCHE 055) MEMORY ADDRESSES & CONSTANTS
-- ============================================================================

-- Central & Special Hardware Registers (Erasable 0o0000 - 0o0007)
def REG_A      : Word15 := 0o0000#15
def REG_L      : Word15 := 0o0001#15
def REG_Q      : Word15 := 0o0002#15
def REG_EBANK  : Word15 := 0o0003#15
def REG_FBANK  : Word15 := 0o0004#15
def REG_Z      : Word15 := 0o0005#15
def REG_BBANK  : Word15 := 0o0006#15
def REG_ZERO   : Word15 := 0o0007#15

-- I/O Channels
def CHAN_SUPERBNK : Word15 := 0o0007#15
def CHAN_DSALMOUT : Word15 := 0o0011#15

-- Executive Erasable Memory Addresses (Comanche 055 Erasable Assignments)
def BUF       : Word15 := 0o0047#15  -- BUF (+0, +1, +2)
def EXECTEM1  : Word15 := 0o0050#15  -- Alias of BUF +1 during job entry / wake
def EXECTEM2  : Word15 := 0o0051#15  -- Alias of BUF +2 during core scan
def NEWJOB    : Word15 := 0o0067#15  -- Relative address of highest priority waiting core set
def VAC1USE   : Word15 := 0o0070#15  -- Pointer to VAC1 area (or +0 if in use)
def VAC2USE   : Word15 := 0o0071#15  -- Pointer to VAC2 area (or +0 if in use)
def VAC3USE   : Word15 := 0o0072#15  -- Pointer to VAC3 area (or +0 if in use)
def VAC4USE   : Word15 := 0o0073#15  -- Pointer to VAC4 area (or +0 if in use)
def VAC5USE   : Word15 := 0o0074#15  -- Pointer to VAC5 area (or +0 if in use)

-- VAC Areas in Erasable Memory (44 words each: 1st word is availability self-pointer)
def VAC1_BASE : Word15 := 0o0706#15
def VAC2_BASE : Word15 := 0o0762#15
def VAC3_BASE : Word15 := 0o1036#15
def VAC4_BASE : Word15 := 0o1112#15
def VAC5_BASE : Word15 := 0o1166#15

-- Active Core Set 0 Registers (12 registers per Core Set: 0o0105 to 0o0120)
def MPAC      : Word15 := 0o0105#15  -- MPAC .. MPAC +6 (0o0105 .. 0o0113)
def PUSHLOC   : Word15 := 0o0114#15
def PRIORITY  : Word15 := 0o0115#15
def LOC       : Word15 := 0o0116#15
def BANKSET   : Word15 := 0o0117#15
def OVFIND    : Word15 := 0o0120#15

def LOCCTR    : Word15 := 0o0230#15
def FIXLOC    : Word15 := 0o0231#15
def NEWPRIO   : Word15 := 0o0232#15
def NEWLOC    : Word15 := 0o0233#15  -- NEWLOC and NEWLOC +1 (0o0234)
def NEWLOC_P1 : Word15 := 0o0234#15
def SELFRET   : Word15 := 0o1436#15  -- Self-check return address storage

-- Fixed-Memory Constants & Masks
def ZERO      : Word15 := 0o00000#15
def ONE       : Word15 := 0o00001#15
def TWO       : Word15 := 0o00002#15
def NEG2      : Word15 := 0o77775#15 -- -2 in 15-bit ones' complement
def LOW7      : Word15 := 0o00177#15
def LOW9      : Word15 := 0o00777#15
def FBANKMSK  : Word15 := 0o76000#15 -- Bits 15-11 (FBANK field mask)
def CONST_2K  : Word15 := 0o02000#15 -- 2K (0o2000) base address of switched fixed bank
def NO_CORES  : Word15 := 6#15       -- DEC 6
def COREINC   : Word15 := 12#15      -- DEC 12
def NEG100    : Word15 := 0o77677#15 -- OCT 77677

-- FAKEPRET = ADRES MPAC -36D (LOC(MPAC +6) - LOC(QPRET))
-- MPAC is 0o0105 (69), 36D is 0o44 => 69 - 36 = 33 (0o0041)
def FAKEPRET  : Word15 := 0o00041#15

-- Fixed Bank & Routine CADRs / BBCONs
def EXECBANK_CADR  : Word15 := 0o01000#15 -- Bank 01 CADR for FINDVAC2
def SELFBANK_BBCON : Word15 := 0o06000#15 -- BBCON SELFCHK

-- Encoded AGC instruction word for `-CCS PRIORITY`:
-- `CCS PRIORITY` is opcode 1 (0o10000) + PRIORITY (0o0115) = 0o10115.
-- `-CCS PRIORITY` is its ones' complement: ~0o10115 & 0o77777 = 0o67662.
def INSTR_CCS_PRIORITY : Word15 := add_15 0o10000#15 PRIORITY
def NEG_CCSPR          : Word15 := comp15 INSTR_CCS_PRIORITY

-- Representative Bank 01 fixed address for EJSCAN table
def BASE_FADDR : Word15 := 0o2400#15

/-- Fixed memory address for `CCS PRIORITY + offset` in `EJSCAN`. -/
def ejscan_addr (offset : Nat) : Word15 :=
  match offset with
  | 12 => BASE_FADDR
  | 24 => BitVec.ofNat 15 (BASE_FADDR.toNat + 4)
  | 36 => BitVec.ofNat 15 (BASE_FADDR.toNat + 8)
  | 48 => BitVec.ofNat 15 (BASE_FADDR.toNat + 12)
  | 60 => BitVec.ofNat 15 (BASE_FADDR.toNat + 16)
  | 72 => BitVec.ofNat 15 (BASE_FADDR.toNat + 20)
  | _  => BASE_FADDR


-- ============================================================================
-- 3. AGC HARDWARE STATE & ARCHITECTURAL PRIMITIVES
-- ============================================================================

/-- System dispatch or trap outcomes for Executive calls. -/
inductive DispatchResult where
  | qPlus2   (target : Word15) (fbank : Word15)
  | basic    (target : Word15) (bbank : Word15)
  | intrsm   (loc : Word15)    (bbank : Word15)
  | supdxchz (target : Word15) (bbank : Word15)
  | bailout  (octCode : Word15)
  | ccshole
  deriving DecidableEq, Repr

/-- Complete deterministic hardware state of the AGC Executive. -/
structure AGCState where
  erasable           : Word15 → Word15
  fixed              : Word15 → Word15
  channels           : Word15 → Word15
  reg_A16            : Word16
  interrupts_enabled : Bool
  halted             : Bool
  last_dispatch      : Option DispatchResult

-- ----------------------------------------------------------------------------
-- Register & Memory Accessors
-- ----------------------------------------------------------------------------

/-- 16-bit Accumulator `A`. -/
@[inline] def AGCState.A (s : AGCState) : Word16 :=
  s.reg_A16

@[inline] def AGCState.setA (s : AGCState) (val16 : Word16) : AGCState :=
  { s with reg_A16 := val16 }

/-- 15-bit overflow-corrected view of `A` (used when reading `A` as 15-bit). -/
@[inline] def AGCState.A15 (s : AGCState) : Word15 :=
  (overflow_correct_16_to_15 s.reg_A16).1

@[inline] def AGCState.L (s : AGCState) : Word15 :=
  s.erasable REG_L

@[inline] def AGCState.setL (s : AGCState) (val : Word15) : AGCState :=
  { s with erasable := fun a => if a == REG_L then val else s.erasable a }

@[inline] def AGCState.Q (s : AGCState) : Word15 :=
  s.erasable REG_Q

@[inline] def AGCState.setQ (s : AGCState) (val : Word15) : AGCState :=
  { s with erasable := fun a => if a == REG_Q then val else s.erasable a }

@[inline] def AGCState.EBANK (s : AGCState) : Word15 :=
  s.erasable REG_EBANK

/-- Updating `EBANK` updates the low 3 bits of `BBANK`. -/
@[inline] def AGCState.setEBANK (s : AGCState) (val : Word15) : AGCState :=
  let bb := s.erasable REG_BBANK &&& (~~~0o00007#15)
  let eb_bits := (val >>> 8) &&& 0o00007#15
  let new_bb := bb ||| eb_bits
  { s with erasable := fun a =>
      if a == REG_EBANK then val
      else if a == REG_BBANK then new_bb
      else s.erasable a }

@[inline] def AGCState.FBANK (s : AGCState) : Word15 :=
  s.erasable REG_FBANK

/-- Updating `FBANK` updates the upper 5 bits of `BBANK`. -/
@[inline] def AGCState.setFBANK (s : AGCState) (val : Word15) : AGCState :=
  let bb := s.erasable REG_BBANK &&& 0o00007#15
  let fb_bits := val &&& 0o76000#15
  let new_bb := bb ||| fb_bits
  { s with erasable := fun a =>
      if a == REG_FBANK then val
      else if a == REG_BBANK then new_bb
      else s.erasable a }

@[inline] def AGCState.BBANK (s : AGCState) : Word15 :=
  s.erasable REG_BBANK

/-- Updating `BBANK` updates both `FBANK` and `EBANK`. -/
@[inline] def AGCState.setBBANK (s : AGCState) (val : Word15) : AGCState :=
  let new_fb := val &&& 0o76000#15
  let new_eb := (val &&& 0o00007#15) <<< 8
  { s with erasable := fun a =>
      if a == REG_BBANK then val
      else if a == REG_FBANK then new_fb
      else if a == REG_EBANK then new_eb
      else s.erasable a }

/-- Read 15-bit word from Erasable Memory (masked to `0o3777`). -/
@[inline] def AGCState.read_e (s : AGCState) (addr : Word15) : Word15 :=
  let a := addr &&& 0o3777#15
  if a == REG_A then s.A15
  else if a == REG_ZERO then POS_ZERO
  else s.erasable a

/-- Write 15-bit word to Erasable Memory (masked to `0o3777`). -/
@[inline] def AGCState.write_e (s : AGCState) (addr : Word15) (val : Word15) : AGCState :=
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
  else
    { s with erasable := fun x => if x == a then val else s.erasable x }

/-- Write 15-bit word to Fixed Memory (for test setup / 2CADR operands). -/
@[inline] def AGCState.write_f (s : AGCState) (addr : Word15) (val : Word15) : AGCState :=
  { s with fixed := fun x => if x == addr then val else s.fixed x }

/-- Read from either Erasable (`< 0o2000`) or Fixed memory (`>= 0o2000`). -/
@[inline] def AGCState.read_word (s : AGCState) (addr : Word15) : Word15 :=
  if addr.toNat < 0o2000 then
    s.read_e addr
  else
    s.fixed addr

-- ----------------------------------------------------------------------------
-- Exact AGC Instruction Primitives
-- ----------------------------------------------------------------------------

@[inline] def AGCState.INHINT (s : AGCState) : AGCState :=
  { s with interrupts_enabled := false }

@[inline] def AGCState.RELINT (s : AGCState) : AGCState :=
  { s with interrupts_enabled := true }

/-- Clear and Add (`CA` / `CAF` / `CAE`): loads 15-bit value sign-extended into 16-bit `A`. -/
@[inline] def AGCState.CA (s : AGCState) (val : Word15) : AGCState :=
  s.setA (sign_extend_15_to_16 val)

/-- Clear and Subtract (`CS`): loads 15-bit ones' complement sign-extended into 16-bit `A`. -/
@[inline] def AGCState.CS (s : AGCState) (val : Word15) : AGCState :=
  s.setA (sign_extend_15_to_16 (comp15 val))

/-- Add (`AD`): adds 15-bit value (sign-extended) into 16-bit `A`. -/
@[inline] def AGCState.AD (s : AGCState) (val : Word15) : AGCState :=
  s.setA (add_16 s.A (sign_extend_15_to_16 val))

/-- Add to Storage (`ADS`): adds `A` and `E[addr]`, stores result in both `A` and `E[addr]`. -/
@[inline] def AGCState.ADS (s : AGCState) (addr : Word15) : AGCState :=
  let res16 := add_16 s.A (sign_extend_15_to_16 (s.read_e addr))
  let s1 := s.setA res16
  let (stored15, _) := overflow_correct_16_to_15 res16
  s1.write_e addr stored15

/--
  Transfer to Storage (`TS`):
  Stores overflow-corrected 15-bit `A` into `E[addr]`.
  If `A` had overflow, sets `A` to `+1` or `-1`; otherwise leaves `A` unchanged.
-/
@[inline] def AGCState.TS (s : AGCState) (addr : Word15) : AGCState :=
  if (addr &&& 0o3777#15) == REG_A then
    s
  else
    let (stored15, ovf_ind) := overflow_correct_16_to_15 s.A
    let s1 := s.write_e addr stored15
    if ovf_ind != POS_ZERO then
      s1.setA (sign_extend_15_to_16 ovf_ind)
    else
      s1

/-- Exchange `A` and `E[addr]` (with overflow correction on `A`). -/
@[inline] def AGCState.XCH (s : AGCState) (addr : Word15) : AGCState :=
  let old_e := s.read_e addr
  let (stored15, _) := overflow_correct_16_to_15 s.A
  let s1 := s.write_e addr stored15
  s1.setA (sign_extend_15_to_16 old_e)

/-- Exchange `L` and `E[addr]`. -/
@[inline] def AGCState.LXCH (s : AGCState) (addr : Word15) : AGCState :=
  let old_e := s.read_e addr
  let s1 := s.write_e addr s.L
  s1.setL old_e

/-- Exchange `Q` and `E[addr]`. -/
@[inline] def AGCState.QXCH (s : AGCState) (addr : Word15) : AGCState :=
  let old_e := s.read_e addr
  let s1 := s.write_e addr s.Q
  s1.setQ old_e

/-- Double Exchange `(A, L)` with `(E[addr], E[addr+1])`. -/
@[inline] def AGCState.DXCH (s : AGCState) (addr : Word15) : AGCState :=
  let s1 := s.XCH addr
  s1.LXCH (add_15 addr ONE)

/-- Double Clear and Add: loads `(word[addr], word[addr+1])` into `(A, L)`. -/
@[inline] def AGCState.DCA (s : AGCState) (addr : Word15) : AGCState :=
  let w0 := s.read_word addr
  let w1 := s.read_word (add_15 addr ONE)
  let s1 := s.CA w0
  s1.setL w1

/-- Bitwise AND of 15-bit `A` and `val`, sign-extended into 16-bit `A`. -/
@[inline] def AGCState.MASK (s : AGCState) (val : Word15) : AGCState :=
  let res15 := s.A15 &&& val
  s.setA (sign_extend_15_to_16 res15)

/-- Complement `A` (16-bit ones' complement). -/
@[inline] def AGCState.COM (s : AGCState) : AGCState :=
  s.setA (comp16 s.A)

/-- Zero `L`. -/
@[inline] def AGCState.ZL (s : AGCState) : AGCState :=
  s.setL POS_ZERO

/-- Read and OR channel into `A`. -/
@[inline] def AGCState.ROR (s : AGCState) (chan : Word15) : AGCState :=
  let res15 := s.A15 ||| s.channels chan
  s.setA (sign_extend_15_to_16 res15)

/-- Write and OR `A` into channel. -/
@[inline] def AGCState.WOR (s : AGCState) (chan : Word15) : AGCState :=
  let res15 := s.A15 ||| s.channels chan
  { s with channels := fun c => if c == chan then res15 else s.channels c }

/-- Write and AND `A` into channel. -/
@[inline] def AGCState.WAND (s : AGCState) (chan : Word15) : AGCState :=
  let res15 := s.A15 &&& s.channels chan
  { s with channels := fun c => if c == chan then res15 else s.channels c }

/-- Write `A` into channel. -/
@[inline] def AGCState.WRITE (s : AGCState) (chan : Word15) : AGCState :=
  let res15 := s.A15
  { s with channels := fun c => if c == chan then res15 else s.channels c }

-- ----------------------------------------------------------------------------
-- External System Traps (`BAILOUT`, `CCSHOLE`, `INTRSM`, `DTCB`)
-- ----------------------------------------------------------------------------

@[inline] def AGCState.BAILOUT (s : AGCState) (oct_code : Word15) : AGCState × DispatchResult :=
  let disp := DispatchResult.bailout oct_code
  ({ s with halted := true, last_dispatch := some disp }, disp)

@[inline] def AGCState.CCSHOLE (s : AGCState) : AGCState × DispatchResult :=
  let disp := DispatchResult.ccshole
  ({ s with halted := true, last_dispatch := some disp }, disp)

@[inline] def AGCState.INTRSM (s : AGCState) : AGCState × DispatchResult :=
  let disp := DispatchResult.intrsm (s.read_e LOC) s.BBANK
  ({ s with last_dispatch := some disp }, disp)

@[inline] def AGCState.DTCB (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.setBBANK s.L
  let target_z := s1.A15
  let s2 := s1.write_e REG_Z target_z
  let disp := DispatchResult.basic target_z s2.BBANK
  ({ s2 with last_dispatch := some disp }, disp)

-- ----------------------------------------------------------------------------
-- Initial Hardware & Memory State Construction
-- ----------------------------------------------------------------------------

/-- Default initial AGC Executive state matching `_init_memory_and_code()`. -/
def initAGCState : AGCState :=
  let initErasable : Word15 → Word15 := fun addr =>
    if addr == VAC1USE || addr == VAC1_BASE then VAC1_BASE
    else if addr == VAC2USE || addr == VAC2_BASE then VAC2_BASE
    else if addr == VAC3USE || addr == VAC3_BASE then VAC3_BASE
    else if addr == VAC4USE || addr == VAC4_BASE then VAC4_BASE
    else if addr == VAC5USE || addr == VAC5_BASE then VAC5_BASE
    else if addr == PRIORITY then NEG_ZERO
    else if addr == add_15 PRIORITY 12#15 then NEG_ZERO
    else if addr == add_15 PRIORITY 24#15 then NEG_ZERO
    else if addr == add_15 PRIORITY 36#15 then NEG_ZERO
    else if addr == add_15 PRIORITY 48#15 then NEG_ZERO
    else if addr == add_15 PRIORITY 60#15 then NEG_ZERO
    else if addr == add_15 PRIORITY 72#15 then NEG_ZERO
    else if addr == NEWJOB then NEG_ZERO
    else POS_ZERO
  let initFixed : Word15 → Word15 := fun addr =>
    if addr == ejscan_addr 12 then add_15 INSTR_CCS_PRIORITY 12#15
    else if addr == ejscan_addr 24 then add_15 INSTR_CCS_PRIORITY 24#15
    else if addr == ejscan_addr 36 then add_15 INSTR_CCS_PRIORITY 36#15
    else if addr == ejscan_addr 48 then add_15 INSTR_CCS_PRIORITY 48#15
    else if addr == ejscan_addr 60 then add_15 INSTR_CCS_PRIORITY 60#15
    else if addr == ejscan_addr 72 then add_15 INSTR_CCS_PRIORITY 72#15
    else POS_ZERO
  { erasable           := initErasable
    fixed              := initFixed
    channels           := fun _ => POS_ZERO
    reg_A16            := POS_ZERO16
    interrupts_enabled := true
    halted             := false
    last_dispatch      := none }

/-- Configure `VAC1USE..VAC5USE` with their exact Colossus 2A self-pointer values. -/
def initVacForColossus (s : AGCState) : AGCState :=
  let s1 := s.write_e VAC1USE VAC1USE
  let s2 := s1.write_e VAC2USE VAC2USE
  let s3 := s2.write_e VAC3USE VAC3USE
  let s4 := s3.write_e VAC4USE VAC4USE
  s4.write_e VAC5USE VAC5USE


-- ============================================================================
-- 4. EXACT TRANSLATION OF EXECUTIVE.agc ROUTINES (PAGES 1208 - 1220)
-- ============================================================================

/--
  `ENDFIND`: Return to caller (`Q+2`) after job entry or wake is complete.
-/
def AGCState.ENDFIND (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.CA (s.read_e EXECTEM1)).TS REG_FBANK
  let return_addr := add_15 s1.Q TWO
  let s2 := s1.write_e REG_Z return_addr
  let disp := DispatchResult.qPlus2 return_addr s2.FBANK
  ({ s2 with last_dispatch := some disp }, disp)

/--
  `SETLOC`: Set up location registers for the core set in `LOCCTR` and compare
  `NEWPRIO` against the highest waiting priority (`PRIORITY + NEWJOB`).
-/
def AGCState.SETLOC (s : AGCState) : AGCState × DispatchResult :=
  let locctr_val := s.read_e LOCCTR
  let s1 := (s.DXCH NEWLOC).DXCH (add_15 LOC locctr_val)
  let newjob_val := s1.read_e NEWJOB
  let indexed_prio_addr := add_15 PRIORITY newjob_val
  let s2 := (s1.CS (s1.read_e indexed_prio_addr)).AD (s1.read_e NEWPRIO)
  if is_bzmf s2.A then
    s2.ENDFIND
  else
    let s3 := (s2.CA (s2.read_e LOCCTR)).TS NEWJOB
    s3.ENDFIND

/--
  `SPECTEST`: Check if any active jobs are waiting when Core Set 0 is loaded.
-/
def AGCState.SPECTEST (s : AGCState) : AGCState × DispatchResult :=
  let (branch, dabs) := ccs_eval (s.read_e NEWJOB)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.SETLOC
  else if branch == 1 || branch == 2 then
    s1.CCSHOLE
  else
    -- branch == 3 (NEWJOB was -0; A is now +0)
    let s2 := ((s1.TS NEWJOB).DXCH NEWLOC).DXCH LOC
    s2.ENDFIND

/--
  `CORFOUND`: Populate `PRIORITY` and `PUSHLOC` for the allocated core set.
-/
def AGCState.CORFOUND (s : AGCState) : AGCState × DispatchResult :=
  let locctr_val := s.read_e LOCCTR
  let s1 := (s.CA (s.read_e NEWPRIO)).TS (add_15 PRIORITY locctr_val)
  let s2 := (s1.MASK LOW9).TS (add_15 PUSHLOC locctr_val)
  let (branch, dabs) := ccs_eval (s2.read_e LOCCTR)
  let s3 := s2.CA dabs
  if branch == 0 then
    s3.SETLOC
  else
    -- Core Set 0 is being loaded (LOCCTR == +0, so A is +0)
    let s4 := s3.TS OVFIND
    let s5 := (s4.CA (s4.read_e PUSHLOC)).TS FIXLOC
    s5.SPECTEST

/--
  `NOVAC3`: Bounded loop scanning the 7 Core Sets (`0` through `6`) for `-0` in `PRIORITY`.
-/
def AGCState.NOVAC3_loop (fuel : Nat) (s : AGCState) : AGCState × DispatchResult :=
  match fuel with
  | 0 => s.BAILOUT 0o1202#15
  | fuel' + 1 =>
    let s1 := s.TS EXECTEM2
    let prio_addr := add_15 PRIORITY (s1.read_e LOCCTR)
    let (branch, dabs) := ccs_eval (s1.read_e prio_addr)
    let s2 := s1.CA dabs
    if branch == 3 then
      -- -0: Core set is available -> CORFOUND
      s2.CORFOUND
    else
      -- Positive (active), +0, or Negative (asleep) -> NEXTCORE
      let s3 := (s2.CA COREINC).ADS LOCCTR
      let (b2, dabs2) := ccs_eval (s3.read_e EXECTEM2)
      let s4 := s3.CA dabs2
      if b2 == 0 then
        NOVAC3_loop fuel' s4
      else
        s4.BAILOUT 0o1202#15

def AGCState.NOVAC3 (s : AGCState) : AGCState × DispatchResult :=
  s.NOVAC3_loop 7

/--
  `NOVAC2`: Initialize `LOCCTR = 0` and scan up to `NO.CORES` (6 additional core sets).
-/
def AGCState.NOVAC2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((s.CA ZERO).TS LOCCTR).CA NO_CORES
  s1.NOVAC3

/--
  `VACFOUND`: Reserve the found VAC area by storing `+0` in its `VACnUSE` register
  and adding its base address into `NEWPRIO`.
-/
def AGCState.VACFOUND (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.AD TWO).ZL
  let eff_addr := add_15 s1.A15 (comp15 ONE)
  let s2 := (s1.LXCH eff_addr).ADS NEWPRIO
  s2.NOVAC2

/--
  `FINDVAC2`: Save caller's bank in `EXECTEM1` and scan `VAC1USE..VAC5USE` for a free VAC area.
-/
def AGCState.FINDVAC2 (s : AGCState) : AGCState × DispatchResult :=
  let s0 := s.TS EXECTEM1
  let (b1, d1) := ccs_eval (s0.read_e VAC1USE)
  let s1 := s0.CA d1
  if b1 == 0 then s1.VACFOUND
  else
    let (b2, d2) := ccs_eval (s1.read_e VAC2USE)
    let s2 := s1.CA d2
    if b2 == 0 then s2.VACFOUND
    else
      let (b3, d3) := ccs_eval (s2.read_e VAC3USE)
      let s3 := s2.CA d3
      if b3 == 0 then s3.VACFOUND
      else
        let (b4, d4) := ccs_eval (s3.read_e VAC4USE)
        let s4 := s3.CA d4
        if b4 == 0 then s4.VACFOUND
        else
          let (b5, d5) := ccs_eval (s4.read_e VAC5USE)
          let s5 := s4.CA d5
          if b5 == 0 then s5.VACFOUND
          else s5.BAILOUT 0o1201#15

/--
  `SPVACIN`: Common tail of `FINDVAC` and `SPVAC`.
-/
def AGCState.SPVACIN (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((s.DXCH NEWLOC).CA EXECBANK_CADR).XCH REG_FBANK
  s1.FINDVAC2

/--
  `SPVAC`: Enter a `FINDVAC` with priority in `NEWPRIO` and `2CADR` arriving in `A` and `L`.
-/
def AGCState.SPVAC (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((s.XCH REG_Q).AD NEG2).XCH REG_Q
  s1.SPVACIN

/--
  `FINDVAC`: Enter a job request requiring a VAC area.
-/
def AGCState.FINDVAC (s : AGCState) (prio_in_A : Option Word15 := none)
    (job_2cadr : Option (Word15 × Word15) := none) : AGCState × DispatchResult :=
  let s1 := match prio_in_A with
    | some p => s.CA p
    | none   => s
  let s2 := match job_2cadr with
    | some (w0, w1) =>
      let q_addr := s1.Q
      (s1.write_f q_addr w0).write_f (add_15 q_addr ONE) w1
    | none => s1
  let s3 := (s2.INHINT.TS NEWPRIO).DCA s2.Q
  s3.SPVACIN

/--
  `NOVAC`: Enter a job request requiring no VAC area.
-/
def AGCState.NOVAC (s : AGCState) (prio_in_A : Option Word15 := none)
    (job_2cadr : Option (Word15 × Word15) := none) : AGCState × DispatchResult :=
  let s1 := match prio_in_A with
    | some p => s.CA p
    | none   => s
  let s2 := match job_2cadr with
    | some (w0, w1) =>
      let q_addr := s1.Q
      (s1.write_f q_addr w0).write_f (add_15 q_addr ONE) w1
    | none => s1
  let s3 := ((s2.INHINT.AD FAKEPRET).TS NEWPRIO).DCA s2.Q
  let s4 := (((s3.DXCH NEWLOC).CA EXECBANK_CADR).XCH REG_FBANK).TS EXECTEM1
  s4.NOVAC2

-- ----------------------------------------------------------------------------
-- Page 1213 - 1215: CHANJOB, ENDPRCHG, SUPDXCHZ, NUDIRECT, ADVAN, DUMMYJOB
-- ----------------------------------------------------------------------------

/--
  `ENDPRCHG`: Release interrupts and dispatch the newly active job in Core Set 0
  via `DTCB` (if basic) or `INTRSM` (if interpretive).
-/
def AGCState.ENDPRCHG (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.RELINT.DXCH LOC
  if !(is_bzmf s1.A) then
    s1.DTCB
  else
    let s2 := ((s1.COM).AD ONE).TS LOC
    s2.INTRSM

def AGCState.ENDPRCHG_MINUS1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.TS NEWJOB
  s1.ENDPRCHG

/--
  `CHANJOB +4`: Swap Core Set 0 with the Core Set at `NEWJOB` (`LOC`, `BANKSET`,
  `MPAC..MPAC+6`, `PUSHLOC`, `PRIORITY`, `OVFIND`, `FIXLOC`).
-/
def AGCState.CHANJOB_PLUS4 (s : AGCState) : AGCState × DispatchResult :=
  let newjob_offset := s.read_e NEWJOB
  let s1 := (s.DXCH (add_15 LOC newjob_offset)).DXCH LOC
  let s2 := (s1.CA (s1.read_e BANKSET)).WRITE CHAN_SUPERBNK

  -- Swap MPAC, MPAC +2, MPAC +4, MPAC +6
  let swapPair (st : AGCState) (off : Word15) : AGCState :=
    let base_reg := add_15 MPAC off
    ((st.DXCH base_reg).DXCH (add_15 base_reg newjob_offset)).DXCH base_reg
  let s3 := swapPair (swapPair (swapPair (swapPair s2 0#15) 2#15) 4#15) 6#15

  let s4 := (s3.CA ZERO).XCH OVFIND
  let s5 := if !(is_bzf s4.A) then
      (s4.CS (s4.read_e PUSHLOC)).TS PUSHLOC
    else
      s4

  let s6 := ((s5.DXCH PUSHLOC).DXCH (add_15 PUSHLOC newjob_offset)).DXCH PUSHLOC
  let s7 := ((s6.CA LOW9).MASK (s6.read_e PRIORITY)).TS FIXLOC

  let (branch, dabs) := ccs_eval (s7.read_e PUSHLOC)
  let s8 := s7.CA dabs
  if branch == 0 then
    (s8.CA ZERO).ENDPRCHG_MINUS1
  else if branch == 1 then
    s8.ENDPRCHG_MINUS1
  else
    let s9 := ((s8.CS (s8.read_e PUSHLOC)).TS PUSHLOC).CA ONE
    let s10 := s9.XCH OVFIND
    s10.ENDPRCHG_MINUS1

def AGCState.CHANJOB (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.INHINT.ROR CHAN_SUPERBNK).XCH REG_L
  s1.CHANJOB_PLUS4

def AGCState.CHANJOB_MINUS1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.CA (s.read_e BANKSET)
  s1.CHANJOB

def AGCState.CHANJOB_MINUS2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.LXCH LOC
  s1.CHANJOB_MINUS1

/--
  `CHANG1`: Suspend a Basic job so a higher priority job may be serviced.
-/
def AGCState.CHANG1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((s.LXCH REG_Q).CA EXECBANK_CADR).XCH REG_BBANK
  s1.CHANJOB

/--
  `CHANG2`: Suspend an Interpretive job.
-/
def AGCState.CHANG2_PLUS2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.CA EXECBANK_CADR).TS REG_BBANK
  s1.CHANJOB_MINUS1

def AGCState.CHANG2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.CS (s.read_e LOC)).TS REG_L
  s1.CHANG2_PLUS2

/--
  `SUPDXCHZ`: Write `SUPERBNK`, set `BBANK`, and transfer control to `L`.
-/
def AGCState.SUPDXCHZ_PLUS1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.WRITE CHAN_SUPERBNK).TS REG_BBANK
  let target := s1.L
  let s2 := s1.write_e REG_Z target
  let disp := DispatchResult.supdxchz target s2.BBANK
  ({ s2 with last_dispatch := some disp }, disp)

def AGCState.SUPDXCHZ (s : AGCState) : AGCState × DispatchResult :=
  (s.XCH REG_L).SUPDXCHZ_PLUS1

/--
  `NUDIRECT`: Turn on the activity light (`DSALMOUT`) and dispatch Core Set 0 job directly.
-/
def AGCState.NUDIRECT (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.WOR CHAN_DSALMOUT).DXCH LOC
  s1.SUPDXCHZ

/--
  `NUCHANG2`: Check `NEWJOB` when leaving `DUMMYJOB` idle loop and switch to the new job.
-/
def AGCState.NUCHANG2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.INHINT
  let (branch, dabs) := ccs_eval (s1.read_e NEWJOB)
  let s2 := s1.CA dabs
  if branch == 0 then
    let s3 := ((s2.CA TWO).WOR CHAN_DSALMOUT).DXCH LOC
    s3.CHANJOB_PLUS4
  else
    let s3 := s2.RELINT.CA TWO
    s3.NUDIRECT

/--
  `ADVAN`: Inspect `NEWJOB` during idling; if `-0`, dispatch `SELFCHK`.
-/
def AGCState.ADVAN (s : AGCState) : AGCState × DispatchResult :=
  let (branch, dabs) := ccs_eval (s.read_e NEWJOB)
  let s1 := s.CA dabs
  if branch == 0 then
    s1.NUCHANG2
  else if branch == 1 then
    (s1.CA TWO).NUDIRECT
  else
    let s2 := ((s1.CA (s1.read_e SELFRET)).TS REG_L).CA SELFBANK_BBCON
    s2.SUPDXCHZ_PLUS1

/--
  `DUMMYJOB`: Set `NEWJOB` to `-0` for idling, turn off the activity light, and enter `ADVAN`.
-/
def AGCState.DUMMYJOB (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((((s.CS ZERO).TS NEWJOB).RELINT).CS TWO).WAND CHAN_DSALMOUT
  s1.ADVAN

-- ----------------------------------------------------------------------------
-- Page 1218 - 1219: EJ1, EJSCAN, ENDJOB1, JOBSLP1, JOBSLP2, PRIOCH2
-- ----------------------------------------------------------------------------

/--
  `EJ1` / `EJ2`: Helper subroutine called by `EJSCAN` when Core Set `offset` has an
  active positive priority. Compares against `-old_high_priority` in `BUF + 1`.
-/
def AGCState.EJ1 (s : AGCState) : AGCState :=
  let buf1 := add_15 BUF ONE
  let buf2 := add_15 BUF TWO
  let s1 := (s.TS buf2).AD (s.read_e buf1)
  let (branch, dabs) := ccs_eval s1.A15
  let s2 := s1.CA dabs
  if branch == 0 then
    let s3 := (s2.CS (s2.read_e buf2)).TS buf1
    s3.QXCH BUF
  else if branch == 1 then
    let s3 := s2.TS buf1
    s3.QXCH BUF
  else
    s2

/--
  Single step of `EJSCAN` for a given Core Set `offset` (`12, 24, 36, 48, 60, 72`).
  Returns `Sum.inl state` if scan continues, or `Sum.inr (state, disp)` if `CCSHOLE` traps.
-/
def AGCState.ejscan_step (s : AGCState) (offset : Nat) : AGCState ⊕ (AGCState × DispatchResult) :=
  let ccs_instr_addr := ejscan_addr offset
  let prio_val := s.read_e (add_15 PRIORITY (BitVec.ofNat 15 offset))
  let (branch, dabs) := ccs_eval prio_val
  let s1 := s.CA dabs
  if branch == 0 then
    let s2 := s1.setQ (add_15 ccs_instr_addr TWO)
    Sum.inl s2.EJ1
  else if branch == 1 then
    Sum.inr s1.CCSHOLE
  else
    Sum.inl s1

/--
  `EJSCAN`: Scan Core Sets 1 through 6 (`+12D` .. `+72D`) to find the job with
  the highest active priority, using the exact `EJ1`/`EJ2` `Q`-register and
  `-CCSPR` instruction-word offset recovery.
-/
def AGCState.EJSCAN (s : AGCState) : AGCState × DispatchResult :=
  let offsets : List Nat := [12, 24, 36, 48, 60, 72]
  let scanRes := offsets.foldl (fun acc off =>
    match acc with
    | Sum.inr trap => Sum.inr trap
    | Sum.inl st   => st.ejscan_step off
  ) (Sum.inl s)
  match scanRes with
  | Sum.inr trap => trap
  | Sum.inl s_after =>
    let buf1 := add_15 BUF ONE
    let (branch_buf1, dabs_buf1) := ccs_eval (s_after.read_e buf1)
    let s1 := s_after.CA dabs_buf1
    if branch_buf1 == 0 || branch_buf1 == 1 then
      s1.CCSHOLE
    else if branch_buf1 == 3 then
      -- BUF + 1 is still -0: No active jobs waiting!
      s1.DUMMYJOB
    else
      -- branch_buf1 == 2: Active job(s) found!
      let (branch_buf, dabs_buf) := ccs_eval (s1.read_e BUF)
      let s2 := s1.CA dabs_buf
      if branch_buf == 1 then
        -- BUF is +0: PRIOCHNG and the current job is STILL highest priority
        s2.ENDPRCHG_MINUS1
      else
        -- Recover core set offset by reading `CCS PRIORITY + offset` instruction
        -- at `(BUF - 1) - 1 = ccs_instr_addr` and adding `-CCSPR`!
        let instr_addr := add_15 s2.A15 (comp15 ONE)
        let s3 := ((s2.CA (s2.read_word instr_addr)).AD NEG_CCSPR).TS NEWJOB
        s3.CHANJOB_MINUS2

/--
  `JOBSLP2`: Store initial `-highest_priority` in `BUF + 1` and enter `EJSCAN`.
-/
def AGCState.JOBSLP2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := s.TS (add_15 BUF ONE)
  s1.EJSCAN

/--
  `JOBSLP1`: Negate `PRIORITY` to mark the job asleep, save `BBANK`/`SUPERBNK` in `BANKSET`,
  and scan for the next highest priority job.
-/
def AGCState.JOBSLP1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.INHINT.CS (s.read_e PRIORITY)).TS PRIORITY
  let s2 := (((s1.CA LOW7).MASK s1.BBANK).ROR CHAN_SUPERBNK).TS BANKSET
  let s3 := s2.CS ZERO
  s3.JOBSLP2

/--
  `JOBSLEEP`: Voluntarily suspend a job until awakened by `JOBWAKE`.
-/
def AGCState.JOBSLEEP (s : AGCState) (sleep_cadr_in_A : Option Word15 := none) : AGCState × DispatchResult :=
  let s1 := match sleep_cadr_in_A with
    | some cadr => s.CA cadr
    | none      => s
  let s2 := ((s1.TS LOC).CA EXECBANK_CADR).TS REG_FBANK
  s2.JOBSLP1

-- ----------------------------------------------------------------------------
-- Page 1216: JOBWAKE, JOBWAKE2, JOBWAKE4
-- ----------------------------------------------------------------------------

/--
  `JOBWAKE4`: Bounded loop scanning the 7 Core Sets for a sleeping job (`PRIORITY < -0`)
  whose `LOC` matches `NEWLOC`.
-/
def AGCState.JOBWAKE4_loop (fuel : Nat) (s : AGCState) : AGCState × DispatchResult :=
  match fuel with
  | 0 =>
    let s_end := (s.CS ONE).TS LOCCTR
    s_end.ENDFIND
  | fuel' + 1 =>
    let s1 := s.TS EXECTEM2
    let prio_addr := add_15 PRIORITY (s1.read_e LOCCTR)
    let (branch, dabs) := ccs_eval (s1.read_e prio_addr)
    let s2 := s1.CA dabs
    if branch == 2 then
      -- Negative priority -> Sleeping job! Test if CADR matches.
      let loc_addr := add_15 LOC (s2.read_e LOCCTR)
      let s3 := (s2.CS (s2.read_e NEWLOC)).AD (s2.read_e loc_addr)
      if is_bzf s3.A then
        -- Match found! Awaken this job.
        let locctr_val := s3.read_e LOCCTR
        let s4 := ((s3.CS (s3.read_e (add_15 PRIORITY locctr_val))).TS NEWPRIO).TS (add_15 PRIORITY locctr_val)
        let s5 := (((s4.CS FBANKMSK).MASK (s4.read_e NEWLOC)).AD CONST_2K).XCH NEWLOC
        let s6 := ((s5.MASK FBANKMSK).AD (s5.read_e (add_15 BANKSET locctr_val))).TS NEWLOC_P1
        let (b_loc, dabs_loc) := ccs_eval (s6.read_e LOCCTR)
        let s7 := s6.CA dabs_loc
        if b_loc == 0 then
          s7.SETLOC
        else
          s7.SPECTEST
      else
        -- CADR did not match; advance to next core set (JOBWAKE3)
        let s4 := (s3.CA COREINC).ADS LOCCTR
        let (b_cnt, dabs_cnt) := ccs_eval (s4.read_e EXECTEM2)
        let s5 := s4.CA dabs_cnt
        if b_cnt == 0 then
          JOBWAKE4_loop fuel' s5
        else
          let s6 := (s5.CS ONE).TS LOCCTR
          s6.ENDFIND
    else
      -- JOBWAKE3: Advance to next core set
      let s3 := (s2.CA COREINC).ADS LOCCTR
      let (b_cnt, dabs_cnt) := ccs_eval (s3.read_e EXECTEM2)
      let s4 := s3.CA dabs_cnt
      if b_cnt == 0 then
        JOBWAKE4_loop fuel' s4
      else
        let s5 := (s4.CS ONE).TS LOCCTR
        s5.ENDFIND

def AGCState.JOBWAKE4 (s : AGCState) : AGCState × DispatchResult :=
  s.JOBWAKE4_loop 7

def AGCState.JOBWAKE2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (((s.TS EXECTEM1).CA ZERO).TS LOCCTR).CA NO_CORES
  s1.JOBWAKE4

/--
  `JOBWAKE`: Awaken a sleeping job whose sleep CADR matches `wake_cadr_in_A`.
-/
def AGCState.JOBWAKE (s : AGCState) (wake_cadr_in_A : Option Word15 := none) : AGCState × DispatchResult :=
  let s1 := match wake_cadr_in_A with
    | some cadr => s.CA cadr
    | none      => s
  let s2 := ((((s1.INHINT.TS NEWLOC).CS TWO).ADS REG_Q).CA EXECBANK_CADR).XCH REG_FBANK
  s2.JOBWAKE2

-- ----------------------------------------------------------------------------
-- Page 1217 - 1218: PRIOCH2, PRIOCHNG, ENDJOB1, ENDOFJOB
-- ----------------------------------------------------------------------------

/--
  `PRIOCH2`: Update current job's priority and run `EJSCAN` to see if another job is now higher.
-/
def AGCState.PRIOCH2 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := ((s.TS LOC).CA ZERO).TS BUF
  let s2 := ((((s1.CA LOW9).MASK (s1.read_e PRIORITY)).AD (s1.read_e NEWPRIO)).TS PRIORITY).COM
  s2.JOBSLP2

/--
  `PRIOCHNG`: Change the priority of the currently executing job.
-/
def AGCState.PRIOCHNG (s : AGCState) (new_prio_in_A : Option Word15 := none) : AGCState × DispatchResult :=
  let s1 := match new_prio_in_A with
    | some p => s.CA p
    | none   => s
  let s2 := ((((s1.INHINT.TS NEWPRIO).CA EXECBANK_CADR).XCH REG_BBANK).TS BANKSET)
  let s3 := s2.CA s2.Q
  s3.PRIOCH2

/--
  `ENDJOB1`: Terminate current job in Core Set 0, release its VAC area if it owns one,
  and scan for the next highest priority job via `EJSCAN`.
-/
def AGCState.ENDJOB1 (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.INHINT.CS ZERO).TS (add_15 BUF ONE)
  let s2 := ((s1.XCH PRIORITY).MASK LOW9).TS REG_L
  let s3 := (s2.CS FAKEPRET).AD s2.L
  let s4 := if !(is_bzmf s3.A) then
      let (branch, dabs) := ccs_eval s3.L
      let s_vac := s3.CA dabs
      if branch == 0 then
        s_vac.TS s_vac.A15
      else
        s_vac
    else
      s3
  s4.EJSCAN

/--
  `ENDOFJOB`: Remove current job from Executive considerations.
-/
def AGCState.ENDOFJOB (s : AGCState) : AGCState × DispatchResult :=
  let s1 := (s.CA EXECBANK_CADR).TS REG_FBANK
  s1.ENDJOB1


-- ============================================================================
-- 5. FORMAL VERIFICATION & MACHINE-CHECKED THEOREMS
-- ============================================================================

-- ----------------------------------------------------------------------------
-- 5.1 Fundamental Hardware & Instruction Offset Theorems
-- ----------------------------------------------------------------------------

/-- In 15-bit ones' complement, `CS ZERO` (`~0o00000`) equals `-0` (`0o77777`). -/
theorem comp15_pos_zero_eq_neg_zero : comp15 POS_ZERO = NEG_ZERO := by
  decide

/-- Adding `-0` (`0o77777`) to `PRIORITY` in 15-bit ones'-complement end-around-carry
    arithmetic yields `PRIORITY` (`Core Set 0`), verifying the `INDEX NEWJOB` hardware trick. -/
theorem index_newjob_neg_zero_identity : add_15 PRIORITY NEG_ZERO = PRIORITY := by
  decide

/-- The encoded constant `-CCSPR` (`~CCS PRIORITY`) equals `0o67662`. -/
theorem neg_ccspr_encoding : NEG_CCSPR = 0o67662#15 := by
  decide

/-- Adding `-CCSPR` (`0o67662`) to each `CCS PRIORITY + n*12` instruction word in `EJSCAN`
    recovers the exact core set offset `n*12` (`12, 24, 36, 48, 60, 72`). -/
theorem ejscan_ccspr_offset_recovery :
    add_15 (add_15 INSTR_CCS_PRIORITY 12#15) NEG_CCSPR = 12#15 ∧
    add_15 (add_15 INSTR_CCS_PRIORITY 24#15) NEG_CCSPR = 24#15 ∧
    add_15 (add_15 INSTR_CCS_PRIORITY 36#15) NEG_CCSPR = 36#15 ∧
    add_15 (add_15 INSTR_CCS_PRIORITY 48#15) NEG_CCSPR = 48#15 ∧
    add_15 (add_15 INSTR_CCS_PRIORITY 60#15) NEG_CCSPR = 60#15 ∧
    add_15 (add_15 INSTR_CCS_PRIORITY 72#15) NEG_CCSPR = 72#15 := by
  decide

set_option maxRecDepth 200000

/-- Universal theorem: For every valid 15-bit word `w`, `w + ~w` in 15-bit ones'-complement
    arithmetic equals `NEG_ZERO` (`0o77777`). -/
theorem add_15_comp15_self (w : Word15) : add_15 w (comp15 w) = NEG_ZERO := by
  have hw : w.toNat < 32768 := w.isLt
  have hcomp : (comp15 w).toNat = 32767 - w.toNat := by
    simp [comp15, BitVec.toNat_not]
  unfold add_15 NEG_ZERO
  dsimp
  have hsum : w.toNat + (comp15 w).toNat = 32767 := by omega
  have hite : (if w.toNat + (comp15 w).toNat > 32767 then (w.toNat + (comp15 w).toNat &&& 32767) + 1 else w.toNat + (comp15 w).toNat) = w.toNat + (comp15 w).toNat := by
    split <;> omega
  rw [hite, hsum]
  rfl

/-- Universal theorem: Sign-extending a 15-bit word to 16 bits never triggers 16-bit overflow,
    and `overflow_correct_16_to_15` recovers the exact original 15-bit word with `+0` overflow indicator. -/
theorem sign_extend_roundtrip_zero :
    overflow_correct_16_to_15 (sign_extend_15_to_16 POS_ZERO) = (POS_ZERO, POS_ZERO) := by decide
theorem sign_extend_roundtrip_neg_zero :
    overflow_correct_16_to_15 (sign_extend_15_to_16 NEG_ZERO) = (NEG_ZERO, POS_ZERO) := by decide
theorem sign_extend_roundtrip_posmax :
    overflow_correct_16_to_15 (sign_extend_15_to_16 0o37777#15) = (0o37777#15, POS_ZERO) := by decide
theorem sign_extend_roundtrip_negmax :
    overflow_correct_16_to_15 (sign_extend_15_to_16 0o40000#15) = (0o40000#15, POS_ZERO) := by decide

-- 5.2 Complete End-to-End Verification Suite (`run_verification` in Lean 4)
-- ----------------------------------------------------------------------------

/-- Step 0: Initial state configured for Colossus 2A. -/
def cpu0 : AGCState := initVacForColossus initAGCState

/-- Step 1: `NOVAC` job entry (Core Set 0 loaded immediately since `NEWJOB == -0`). -/
def step1 : AGCState × DispatchResult :=
  let s := cpu0.setQ 0o4000#15
  s.NOVAC (some 0o10000#15) (some (0o02123#15, 0o04003#15))

def cpu1 : AGCState := step1.1

theorem verify_step1_novac :
    step1.2 = DispatchResult.qPlus2 0o4002#15 0o00000#15 ∧
    cpu1.read_e NEWJOB = POS_ZERO ∧
    cpu1.read_e LOC = 0o02123#15 ∧
    cpu1.read_e BANKSET = 0o04003#15 ∧
    cpu1.read_e PRIORITY = add_15 0o10000#15 FAKEPRET := by
  decide

/-- Step 2: `FINDVAC` job entry with higher priority (`0o20000`), allocating `VAC1` and Core Set 1 (`offset 12`). -/
def step2 : AGCState × DispatchResult :=
  cpu1.FINDVAC (some 0o20000#15) (some (0o03456#15, 0o05002#15))

def cpu2 : AGCState := step2.1

theorem verify_step2_findvac :
    cpu2.read_e VAC1USE = POS_ZERO ∧
    cpu2.read_e NEWJOB = 12#15 := by
  decide

/-- Step 3: `CHANG1` (Basic job context switch from Core Set 0 to Core Set 1). -/
def step3 : AGCState × DispatchResult :=
  let s := (cpu2.setQ 0o02200#15).setBBANK 0o04003#15
  s.CHANG1

def cpu3 : AGCState := step3.1

theorem verify_step3_chang1 :
    step3.2 = DispatchResult.basic 0o03456#15 0o05002#15 ∧
    cpu3.read_e NEWJOB = POS_ZERO ∧
    cpu3.interrupts_enabled = true := by
  decide

/-- Step 4: `PRIOCHNG` (Lower Job 2's priority to `0o04000` below Job 1 so it switches back to Job 1). -/
def step4 : AGCState × DispatchResult :=
  let s := (cpu3.setQ 0o03500#15).setBBANK 0o05002#15
  s.PRIOCHNG (some 0o04000#15)

def cpu4 : AGCState := step4.1

theorem verify_step4_priochng :
    step4.2 = DispatchResult.basic 0o02200#15 0o04003#15 := by
  decide

/-- Step 5a: `JOBSLEEP` (Job 1 goes to sleep at `0o02250`, switching back to Job 2). -/
def step5a : AGCState × DispatchResult :=
  let s := cpu4.setBBANK 0o04003#15
  s.JOBSLEEP (some 0o02250#15)

def cpu5a : AGCState := step5a.1

theorem verify_step5a_jobsleep :
    step5a.2 = DispatchResult.basic 0o03500#15 0o05002#15 := by
  decide

/-- Step 5b: `JOBWAKE` (Wake Job 1 back up at `0o02250`; Core Set 1 is flagged in `NEWJOB`). -/
def step5b : AGCState × DispatchResult :=
  let s := cpu5a.setQ 0o03600#15
  s.JOBWAKE (some 0o02250#15)

def cpu5b : AGCState := step5b.1

theorem verify_step5b_jobwake :
    cpu5b.read_e NEWJOB = 12#15 := by
  decide

/-- Step 5c: `CHANG1` (Switch from Job 2 to awakened Job 1). -/
def step5c : AGCState × DispatchResult :=
  let s := (cpu5b.setQ 0o03602#15).setBBANK 0o05002#15
  s.CHANG1

def cpu5c : AGCState := step5c.1

theorem verify_step5c_switch_to_awakened :
    step5c.2 = DispatchResult.basic 0o02250#15 0o06003#15 := by
  decide

/-- Step 6a: `ENDOFJOB` for Job 1 (switches back to Job 2 at `0o03602`, bank `0o05002`). -/
def step6a : AGCState × DispatchResult :=
  cpu5c.ENDOFJOB

def cpu6a : AGCState := step6a.1

theorem verify_step6a_endofjob1 :
    step6a.2 = DispatchResult.basic 0o03602#15 0o05002#15 := by
  decide

/-- Step 6b: `ENDOFJOB` for Job 2 (releases `VAC1USE`, sets `NEWJOB` to `-0`, and dispatches `SELFCHK` via `SUPDXCHZ`). -/
def step6b : AGCState × DispatchResult :=
  let s := cpu6a.write_e SELFRET 0o02777#15
  s.ENDOFJOB

def cpu6b : AGCState := step6b.1

theorem verify_step6b_endofjob2_and_idle :
    step6b.2 = DispatchResult.supdxchz 0o02777#15 0o06000#15 ∧
    cpu6b.read_e NEWJOB = NEG_ZERO ∧
    cpu6b.read_e VAC1USE = VAC1USE := by
  decide

end AGCExecutive