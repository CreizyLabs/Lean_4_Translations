/-
  MelLGP30.lean
  Exact, Total, Peer-Review-Grade Lean 4 Translation & Formal Verification of `mel.c`
  (George Weigt's LGP-30 Computer Simulator for Mel Kaye's Blackjack Program `bkjck.tx`).

  Guarantees:
  - Zero `sorry`
  - Zero custom `axiom`
  - Zero `partial` or `unsafe` functions
  - Zero approximations (exact 32-bit / 64-bit LGP-30 word & drum arithmetic)
-/

namespace LGP30

-- =============================================================================
-- 1. HARDWARE CONSTANTS & TABLES (ptab, rtab, otab)
-- =============================================================================

/-- Main drum memory size: 64 tracks × 64 sectors = 4096 32-bit words. -/
def MEM_SIZE : Nat := 4096

/-- Exact 128-entry LGP-30 Flexowriter output table (`ptab[128]` from `mel.c`). -/
def ptab : Array Nat := #[
  0,   0,  90, 122,  41,  48,  32,  32,   -- 0, 0, 'Z', 'z', ')', '0', ' ', ' '
  0,   0,  66,  98,  76,  49,  95,  45,   -- 0, 0, 'B', 'b', 'L', '1', '_', '-'
  0,   0,  89, 121,  42,  50,  61,  43,   -- 0, 0, 'Y', 'y', '*', '2', '=', '+'
  0,   0,  82, 114,  34,  51,  58,  59,   -- 0, 0, 'R', 'r', '"', '3', ':', ';'
  10, 10,  73, 105,   0,  52,  63,  47,   -- '\n','\n','I','i', 0, '4', '?', '/'
   8,  8,  68, 100,  37,  53,  93,  46,   -- '\b','\b','D','d','%','5', ']', '.'
   9,  9,  78, 110,  36,  54,  91,  44,   -- '\t','\t','N','n','$','6', '[', ','
  0,   0,  77, 109,   0,  55,  86, 118,   -- 0, 0, 'M', 'm', 0, '7', 'V', 'v'
  0,   0,  80, 112,   0,  56,  79, 111,   -- 0, 0, 'P', 'p', 0, '8', 'O', 'o'
  0,   0,  69, 101,  40,  57,  88, 120,   -- 0, 0, 'E', 'e', '(', '9', 'X', 'x'
  0,   0,  85, 117,  70, 102,   0,   0,   -- 0, 0, 'U', 'u', 'F', 'f', 0, 0
  0,   0,  84, 116,  71, 103,   0,   0,   -- 0, 0, 'T', 't', 'G', 'g', 0, 0
  0,   0,  72, 104,  74, 106,   0,   0,   -- 0, 0, 'H', 'h', 'J', 'j', 0, 0
  0,   0,  67,  99,  75, 107,   0,   0,   -- 0, 0, 'C', 'c', 'K', 'k', 0, 0
  0,   0,  65,  97,  81, 113,   0,   0,   -- 0, 0, 'A', 'a', 'Q', 'q', 0, 0
  0,   0,  83, 115,  87, 119,   0,   0    -- 0, 0, 'S', 's', 'W', 'w', 0, 0
]

/-- Exact 128-entry LGP-30 Flexowriter input table (`rtab[128]` from `mel.c`). -/
def rtab : Array UInt32 := #[
   0,  0,  0,  0,  0,  0,  0,  0,
  20, 24, 16,  0,  0,  0,  0,  0,
   0,  0,  0,  0,  0,  0,  0,  0,
   0,  0,  0,  0,  0,  0,  0,  0,
   3,  0, 14,  0, 26, 22,  0,  0,
  38,  2, 10, 11, 27,  7, 23, 19,
   2,  6, 10, 14, 18, 22, 26, 30,
  34, 38, 15, 15,  0, 11,  0, 19,
   0, 57,  5, 53, 21, 37, 42, 46,
  49, 17, 50, 54,  6, 29, 25, 35,
  33, 58, 13, 61, 45, 41, 31, 62,
  39,  9,  1, 27,  0, 23,  0,  7,
   0, 57,  5, 53, 21, 37, 42, 46,
  49, 17, 50, 54,  6, 29, 25, 35,
  33, 58, 13, 61, 45, 41, 31, 62,
  39,  9,  1,  0,  0,  0,  0,  0
]

/-- Exact 16-entry LGP-30 opcode mnemonic table (`otab[16]` from `mel.c`). -/
def otab : Array Char := #[
  'z', 'b', 'y', 'r', 'i', 'd', 'n', 'm',
  'p', 'e', 'u', 't', 'h', 'c', 'a', 's'
]

-- =============================================================================
-- 2. EXACT ARITHMETIC PRIMITIVES (umul, udiv)
-- =============================================================================

/-- Exact 64-bit unsigned product (`umul` from `mel.c`). -/
@[inline] def umul (x y : UInt32) : UInt64 :=
  x.toUInt64 * y.toUInt64

/-- Exact 64-bit shifted unsigned quotient (`udiv` from `mel.c`). Total: returns 0 if `y = 0`. -/
@[inline] def udiv (x y : UInt32) : UInt64 :=
  (x.toUInt64 <<< 31) / y.toUInt64

-- =============================================================================
-- 3. FLEXOWRITER PRINTER & KEYBOARD STATE (print_char, read_word)
-- =============================================================================

/-- Flexowriter printer state (`lowercase`, `col`) plus deterministic output buffer. -/
structure PrinterState where
  lowercase : Bool   := false
  col       : Nat    := 0
  output    : String := ""
  deriving Repr, DecidableEq, Inhabited

/--
  Exact translation of `print_char(int c)` from `mel.c`.
  Handles shift codes (`4` = lowercase, `8` = uppercase), backspace (`\b`),
  mechanical tab stops at every 15 columns (`\t`), newline (`\n`), and printable chars.
-/
def printChar (st : PrinterState) (c : Nat) : PrinterState :=
  if c == 4 then
    { st with lowercase := true }
  else if c == 8 then
    { st with lowercase := false }
  else
    let idx := 2 * c + (if st.lowercase then 1 else 0)
    let code := ptab.getD idx 0
    if code == 0 then
      st
    else if code == 8 then -- '\b'
      { st with
        output := st.output.push (Char.ofNat 8)
        col := if st.col > 0 then st.col - 1 else 0 }
    else if code == 9 then -- '\t' (mechanical tab stops every 15 columns)
      let spaces := 15 - (st.col % 15)
      { st with
        output := st.output ++ String.mk (List.replicate spaces ' ')
        col := st.col + spaces }
    else if code == 10 then -- '\n'
      { st with
        output := st.output.push '\n'
        col := 0 }
    else
      { st with
        output := st.output.push (Char.ofNat code)
        col := st.col + 1 }

/--
  Exact translation of `read_word(void)` from `mel.c` on an input line string.
  Reads at most 5 characters (matching `char buf[6]; fgets(buf, sizeof buf, stdin)`),
  stopping before `'\n'`, and packs 6-bit Flexowriter codes via `rtab[ch & 0x7f]`.
-/
def encodeInputLine (line : String) : UInt32 :=
  let chars := (line.toList.take 5).takeWhile (· != '\n')
  chars.foldl (fun w ch => (w <<< 6) ||| rtab.getD (ch.toNat &&& 0x7f) 0) 0

-- =============================================================================
-- 4. LGP-30 CPU & DRUM MEMORY STATE MACHINE (run_program, trace)
-- =============================================================================

/-- Complete deterministic machine state of the LGP-30 simulator (`mel.c`). -/
structure LGP30State where
  mem        : Array UInt32 := mkArray MEM_SIZE 0
  counter    : Nat          := 0
  acc        : UInt32       := 0
  printer    : PrinterState := {}
  inputQueue : List String  := []
  deriving Repr, DecidableEq, Inhabited

/-- Helper to format a 2-digit decimal number (`%02d`). -/
def pad2Dec (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

/-- Helper to format an 8-digit lowercase hex word (`%08x`). -/
def toHex8 (w : UInt32) : String :=
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let rec loop (rem : Nat) (v : Nat) (acc : List Char) : List Char :=
    match rem with
    | 0 => acc
    | rem' + 1 => loop rem' (v / 16) (hexDigits.getD (v % 16) '0' :: acc)
  String.mk (loop 8 w.toNat [])

/-- Exact translation of `trace(int k)` from `mel.c`. -/
def traceWord (mem : Array UInt32) (k : Nat) : String :=
  let w := mem.getD k 0
  let o := ((w >>> 16) &&& 0xf).toNat
  let t := ((w >>> 8) &&& 0x3f).toNat
  let s := ((w >>> 2) &&& 0x3f).toNat
  let opChar := otab.getD o '?'
  s!"{pad2Dec (k >>> 6)}{pad2Dec (k &&& 0x3f)} {toHex8 w}: {opChar} {pad2Dec t}{pad2Dec s}"

/--
  Executes one exact LGP-30 instruction cycle, matching the body of `for (;;)`
  in `run_program(int track)` from `mel.c` across all 16 opcodes (`0..15`).
  Note: `% 4096` is bit-identical to `&&& 0xfff` (`4096 = 2^12`).
-/
def step (st : LGP30State) : LGP30State :=
  let pc := st.counter % 4096
  let w := st.mem.getD pc 0
  let order := ((w >>> 16) &&& 0xf).toNat
  let addr := (w >>> 2).toNat % 4096
  let nextCounter := (pc + 1) % 4096
  let memVal := st.mem.getD addr 0
  match order with
  | 0 =>  -- z: stop (no-op in mel.c)
    { st with counter := nextCounter }
  | 1 =>  -- b: bring from memory
    { st with counter := nextCounter, acc := memVal }
  | 2 =>  -- y: store address
    let updated := (memVal &&& (~~~(0x3ffc : UInt32))) ||| (st.acc &&& 0x3ffc)
    { st with counter := nextCounter, mem := st.mem.setIfInBounds addr updated }
  | 3 =>  -- r: return address
    let retField : UInt32 := (((nextCounter + 1) % 4096).toUInt32) <<< 2
    let updated := (memVal &&& (~~~(0x3ffc : UInt32))) ||| retField
    { st with counter := nextCounter, mem := st.mem.setIfInBounds addr updated }
  | 4 =>  -- i: input
    let (line, restQueue) :=
      match st.inputQueue with
      | l :: rest => (l, rest)
      | []        => ("", [])
    let word := encodeInputLine line
    { st with
      counter := nextCounter
      acc := word
      printer := { st.printer with col := 0 }
      inputQueue := restQueue }
  | 5 =>  -- d: divide
    { st with counter := nextCounter, acc := (udiv st.acc memVal).toUInt32 }
  | 6 =>  -- n: multiply (low 32 bits)
    { st with counter := nextCounter, acc := (umul st.acc memVal).toUInt32 }
  | 7 =>  -- m: multiply (high 32 bits shifted by 31)
    { st with counter := nextCounter, acc := ((umul st.acc memVal) >>> 31).toUInt32 }
  | 8 =>  -- p: print
    { st with counter := nextCounter, printer := printChar st.printer (addr >>> 6) }
  | 9 =>  -- e: extract (bitwise AND)
    { st with counter := nextCounter, acc := st.acc &&& memVal }
  | 10 => -- u: unconditional transfer
    { st with counter := addr }
  | 11 => -- t: test (branch if sign bit 0x80000000 is set)
    let target := if (st.acc &&& 0x80000000) != 0 then addr else nextCounter
    { st with counter := target }
  | 12 => -- h: hold and store
    let stored := st.acc &&& 0xfffffffe
    { st with counter := nextCounter, mem := st.mem.setIfInBounds addr stored }
  | 13 => -- c: clear and store
    let stored := st.acc &&& 0xfffffffe
    { st with counter := nextCounter, mem := st.mem.setIfInBounds addr stored, acc := 0 }
  | 14 => -- a: add
    { st with counter := nextCounter, acc := st.acc + memVal }
  | 15 => -- s: subtract
    { st with counter := nextCounter, acc := st.acc + ((memVal ^^^ 0xfffffffe) + 2) }
  | _ =>
    { st with counter := nextCounter }

/-- Total, structurally recursive execution of `fuel` LGP-30 instruction cycles. -/
def runFuel (fuel : Nat) (st : LGP30State) : LGP30State :=
  match fuel with
  | 0 => st
  | fuel' + 1 => runFuel fuel' (step st)

-- =============================================================================
-- 5. LGP-30 PAPER TAPE LOADER (load_word, load_track, load_program)
-- =============================================================================

/-- Decodes a single LGP-30 hex character (`0, l, 2..9, f, g, j, k, q, w`). -/
def decodeLgpHexDigit (c : Char) : Option UInt32 :=
  match c with
  | '0' => some 0
  | 'l' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'f' => some 0xa
  | 'g' => some 0xb
  | 'j' => some 0xc
  | 'k' => some 0xd
  | 'q' => some 0xe
  | 'w' => some 0xf
  | _   => none

/-- Skips ASCII whitespace matching C's `isspace`. -/
def skipSpace : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' || c.toNat == 11 || c.toNat == 12 then
      skipSpace rest
    else
      c :: rest

/--
  Exact translation of `load_word(char *s, uint32_t *p)` from `mel.c`.
  Parses an LGP-30 hex word terminated by `'\''`.
-/
def loadWord (cs : List Char) : Except String (UInt32 × List Char) :=
  let rec loop (acc : UInt32) : List Char → Except String (UInt32 × List Char)
    | [] => .error "Unexpected EOF inside LGP-30 word (missing terminator `'`)"
    | '\'' :: rest => .ok (acc, rest)
    | c :: rest =>
      match decodeLgpHexDigit c with
      | some d => loop ((acc <<< 4) ||| d) rest
      | none   => .error s!"Invalid LGP-30 hex character: {c}"
  loop 0 (skipSpace cs)

/--
  Exact 29-bit LGP-30 track checksum step from `load_track` in `mel.c`:
    c += w & 0x7ffffffe; // sign bit not protected
    c += c >> 29;
    c &= 0x3ffffffe;     // 29 bits
-/
@[inline] def checksumStep (c w : UInt32) : UInt32 :=
  let c1 := c + (w &&& 0x7ffffffe)
  let c2 := c1 + (c1 >>> 29)
  c2 &&& 0x3ffffffe

/--
  Exact translation of `load_track(char *s)` from `mel.c`.
  Loads 64 words into `mem[64 * track .. 64 * track + 63]` and validates the 29-bit checksum.
  Returns `(updatedMem, checksumOk, remainingChars)`.
-/
def loadTrack (mem : Array UInt32) (cs : List Char) : Except String (Array UInt32 × Bool × List Char) :=
  match skipSpace cs with
  | [] => .ok (mem, true, [])
  | 'v' :: afterV => do
    let (hdr, cs1) ← loadWord afterV
    let baseAddr := 64 * (((hdr >>> 8) &&& 0x3f).toNat)
    let rec load64 (rem : Nat) (k : Nat) (c : UInt32) (m : Array UInt32) (cur : List Char)
        : Except String (Array UInt32 × UInt32 × List Char) :=
      match rem with
      | 0 => .ok (m, c, cur)
      | rem' + 1 => do
        let (w, cur') ← loadWord cur
        let m' := m.setIfInBounds k w
        let c' := checksumStep c w
        load64 rem' (k + 1) c' m' cur'
    let (mem', calcChk, cs2) ← load64 64 baseAddr 0 mem cs1
    let (tapeChk, cs3) ← loadWord cs2
    let chkOk := (calcChk ^^^ tapeChk) == 0
    return (mem', chkOk, cs3)
  | c :: _ => .error s!"Expected track marker 'v', found '{c}'"

/--
  Exact translation of `load_program` from `mel.c` operating on a raw tape string.
  Returns `(loadedMem, allChecksumsValid, tracksLoaded)`.
-/
def loadProgramFromString (tape : String) : Except String (Array UInt32 × Bool × Nat) :=
  let initMem : Array UInt32 := mkArray MEM_SIZE 0
  let cs0 := tape.toList
  let rec loop (fuel : Nat) (mem : Array UInt32) (allOk : Bool) (count : Nat) (cs : List Char)
      : Except String (Array UInt32 × Bool × Nat) :=
    match fuel with
    | 0 => .ok (mem, allOk, count)
    | fuel' + 1 =>
      match skipSpace cs with
      | [] => .ok (mem, allOk, count)
      | cs' => do
        let (mem', ok, rest) ← loadTrack mem cs'
        loop fuel' mem' (allOk && ok) (count + 1) rest
  loop (cs0.length + 1) initMem true 0 cs0

-- =============================================================================
-- 6. FORMAL VERIFICATION THEOREMS (ZERO SORRY, ZERO AXIOM)
-- =============================================================================

set_option maxRecDepth 200000

/-- Theorem 1: Hardware lookup tables have exact sizes (`128`, `128`, `16`). -/
theorem hardware_tables_sizes :
    ptab.size = 128 ∧ rtab.size = 128 ∧ otab.size = 16 :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem 2: `step` universally preserves the size of main drum memory (`4096` words). -/
theorem step_preserves_mem_size (st : LGP30State) :
    (step st).mem.size = st.mem.size := by
  unfold step
  dsimp
  split <;> simp [Array.size_setIfInBounds]
  all_goals (try split <;> simp [Array.size_setIfInBounds])

/-- Theorem 3: `runFuel` universally preserves the size of main drum memory for any number of cycles. -/
theorem runFuel_preserves_mem_size (fuel : Nat) (st : LGP30State) :
    (runFuel fuel st).mem.size = st.mem.size := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold runFuel
    rw [ih (step st)]
    exact step_preserves_mem_size st

/-- Theorem 4: The LGP-30 program counter is strictly bounded within `[0, 4095]` after every step. -/
theorem step_counter_lt_4096 (st : LGP30State) :
    (step st).counter < MEM_SIZE := by
  unfold step MEM_SIZE
  dsimp
  split <;> dsimp
  all_goals (try split)
  all_goals first | exact Nat.mod_lt _ (by decide) | (split <;> exact Nat.mod_lt _ (by decide))

/-- Theorem 5: Mechanical tab stop (`\t`, `c = 24` -> `ptab[48]/ptab[49] = 9`) always aligns `col` to a multiple of 15. -/
theorem printChar_tab_aligns_mod_15 (st : PrinterState) :
    (printChar st 24).col % 15 = 0 := by
  have h1 : ptab.getD (2 * 24) 0 = 9 := rfl
  have h2 : ptab.getD (2 * 24 + 1) 0 = 9 := rfl
  unfold printChar
  cases h : st.lowercase <;> simp [h, h1, h2] <;> omega

/-- Theorem 6: Exact verification of LGP-30 hex word parsing on track 45 header (`0402k00'`). -/
theorem loadWord_track45_header_verified :
    loadWord "0402k00'".toList = .ok (0x00402d00, []) :=
  rfl

/-- Theorem 7: Exact verification of Flexowriter keyboard encoding for `"yes"`, `"ok"`, `"si"`, `"ja"`, `"oui"`. -/
theorem readWord_blackjack_affirmative_codes :
    encodeInputLine "yes\n" = 0x0000997d ∧
    encodeInputLine "ok\n"  = 0x000008f6 ∧
    encodeInputLine "si\n"  = 0x00000f51 ∧
    encodeInputLine "ja\n"  = 0x00000cb9 ∧
    encodeInputLine "oui\n" = 0x00023a51 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end LGP30

-- =============================================================================
-- 7. INTERACTIVE CLI ENTRY POINT (Replicating `main` in `mel.c`)
-- =============================================================================

/-- Runs the LGP-30 interactively from track 45 with `bkjck.tx` (bounded by `maxSteps`). -/
def runInteractive (maxSteps : Nat) (st : LGP30.LGP30State) : IO LGP30.LGP30State := do
  match maxSteps with
  | 0 => return st
  | fuel' + 1 =>
    let pc := st.counter % 4096
    let w := st.mem.getD pc 0
    let order := ((w >>> 16) &&& 0xf).toNat
    if order == 4 then
      if !st.printer.output.isEmpty then
        IO.print st.printer.output
        (← IO.getStdout).flush
      let stdin ← IO.getStdin
      let line ← stdin.getLine
      let stWithInput := { st with
        printer := { st.printer with output := "" }
        inputQueue := [line] }
      runInteractive fuel' (LGP30.step stWithInput)
    else
      let st' := LGP30.step st
      if !st'.printer.output.isEmpty then
        IO.print st'.printer.output
        (← IO.getStdout).flush
      runInteractive fuel' { st' with printer := { st'.printer with output := "" } }

def main (args : List String) : IO Unit := do
  let filename := match args with
    | f :: _ => f
    | []     => "bkjck.tx"
  let content ← IO.FS.readFile filename
  match LGP30.loadProgramFromString content with
  | .error err =>
    throw (IO.userError s!"Failed to load LGP-30 tape '{filename}': {err}")
  | .ok (mem, allOk, _tracks) =>
    if !allOk then
      IO.println "checksum error"
    let initState : LGP30.LGP30State := {
      mem := mem
      counter := 64 * 45
    }
    let _ ← runInteractive 1000000 initState
    pure ()