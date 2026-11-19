/-
  NatherStoryOfMel.lean
  Exact, Total, Peer-Review-Grade Lean 4 Archival Specification & Machine-Checked Formalization
  of Ed Nather's May 21, 1983 Usenet Article (`nather.txt`):
  "Real Programmers Don't Use Fortran, Either!" (The Story of Mel, a Real Programmer).

  Formalizes:
  1. Verbatim Usenet Archival Header & Historical Record Metadata (`nather.txt`)
  2. RPC-4000 Revolving Drum Timing Model ("Optimum" vs. "Most Pessimum" Delay Proofs)
  3. Console Sense Switch & Mel's Inverted Cheat Test
  4. Mel's Legendary Testless Self-Modifying Loop & Universal Carry-Overflow Mutation Proof
     (Proving universally via `omega` that incrementing an instruction at top-of-memory with
      the index-register bit set carries straight into `opcode + 1` -> `JUMP 0` with zero test!)

  Guarantees:
  - Zero `sorry`
  - Zero custom `axiom`
  - Zero `partial` or `unsafe` functions
  - Zero approximations
-/

namespace StoryOfMel

-- =============================================================================
-- 1. VERBATIM USENET ARCHIVAL RECORD (`nather.txt`)
-- =============================================================================

/-- Exact Usenet RFC-822 / B-News archival metadata from `nather.txt`. -/
structure UsenetRecord where
  fromAddr     : String
  relayVersion : String
  path         : String
  newsgroups   : String
  subject      : String
  messageId    : String
  date         : String
  articleId    : String
  posted       : String
  dateReceived : String
  lineCount    : Nat
  title        : String
  deriving Repr, DecidableEq, Inhabited

def natherRecord : UsenetRecord := {
  fromAddr     := "nather@utastro.UUCP"
  relayVersion := "version B 2.10 5/3/83; site cbosgd.UUCP"
  path         := "cbosgd!mhuxi!mhuxt!eagle!harpo!seismo!hao!cires!nbires!ut-ngp!utastro!nather"
  newsgroups   := "net.followup"
  subject      := "re: Real Programmers ..."
  messageId    := "<355@utastro.UUCP>"
  date         := "Sat, 21-May-83 14:21:33 EDT"
  articleId    := "utastro.355"
  posted       := "Sat May 21 14:21:33 1983"
  dateReceived := "Sun, 22-May-83 19:18:59 EDT"
  lineCount    := 250
  title        := "Real Programmers Don't Use Fortran, Either!"
}

-- =============================================================================
-- 2. RPC-4000 REVOLVING DRUM TIMING MODEL ("OPTIMUM" vs "MOST PESSIMUM")
-- =============================================================================

/--
  Number of sectors per revolution on the Royal McBee RPC-4000 magnetic drum (`64` sectors/track).
-/
def DRUM_SECTORS : Nat := 64

/--
  Rotational latency (in drum sector times) when the read head is at `headSector`
  after finishing an instruction and the next instruction is placed at `nextSector`:
  - `0` sectors wait = **Optimum** (arriving right under the read head)
  - `DRUM_SECTORS - 1` (`63`) sectors wait = **Most Pessimum** (just *past* the read head,
    forcing nearly a full revolution — Mel's Flexowriter time-delay technique without delay loops).
-/
def drumLatency (headSector nextSector : Nat) : Nat :=
  (nextSector + DRUM_SECTORS - (headSector % DRUM_SECTORS)) % DRUM_SECTORS

/-- Optimum placement: next instruction arrives right at `headSector`. -/
def optimumSector (headSector : Nat) : Nat :=
  headSector % DRUM_SECTORS

/-- Most Pessimum placement: next instruction is placed 1 sector *past* (behind) `headSector`. -/
def mostPessimumSector (headSector : Nat) : Nat :=
  (headSector + DRUM_SECTORS - 1) % DRUM_SECTORS

/--
  **Theorem 1 (Optimum Placement Yields Zero Rotational Wait):**
  For any read-head position `h`, placing the next instruction at `optimumSector h`
  achieves exact latency `0`.
-/
theorem optimum_latency_is_zero (h : Nat) :
    drumLatency h (optimumSector h) = 0 := by
  unfold drumLatency optimumSector DRUM_SECTORS
  omega

/--
  **Theorem 2 (Most Pessimum Placement Yields Maximum Rotational Wait = 63 Sectors):**
  For any read-head position `h`, placing the next instruction just past the read head
  (`mostPessimumSector h`) forces the maximum delay of `DRUM_SECTORS - 1 = 63` sectors,
  which dominates every possible placement `s`.
-/
theorem most_pessimum_latency_is_max (h s : Nat) :
    drumLatency h (mostPessimumSector h) = DRUM_SECTORS - 1 ∧
    drumLatency h s ≤ drumLatency h (mostPessimumSector h) := by
  unfold drumLatency mostPessimumSector DRUM_SECTORS
  constructor <;> omega

-- =============================================================================
-- 3. CONSOLE SENSE SWITCH & MEL'S INVERTED CHEAT TEST
-- =============================================================================

/-- Blackjack game outcome mode controlled by the console sense switch. -/
inductive BlackjackOutcome where
  | fairGame
  | customerWins
  | houseCheatsAndWins
  deriving Repr, DecidableEq, Inhabited

/-- What the Sales Department requested vs. what Mel actually coded. -/
def salesRequestedBehavior (senseSwitchOn : Bool) : BlackjackOutcome :=
  if senseSwitchOn then .customerWins else .fairGame

/--
  Mel's "uncontrollably ethical subconscious" inverted the sense-switch test:
  when the console sense switch is turned ON, the program cheats and wins every time.
-/
def melActualBehavior (senseSwitchOn : Bool) : BlackjackOutcome :=
  if senseSwitchOn then .houseCheatsAndWins else .fairGame

/--
  **Theorem 3 (Mel's Sense Switch Inversion):**
  When the sense switch is OFF, Mel's program matches a fair game;
  when the sense switch is ON, Mel's program never lets the customer win via the cheat switch.
-/
theorem mel_sense_switch_ethical_inversion :
    melActualBehavior false = .fairGame ∧
    melActualBehavior true = .houseCheatsAndWins ∧
    melActualBehavior true ≠ salesRequestedBehavior true := by
  decide

-- =============================================================================
-- 4. RPC-4000 ONE-PLUS-ONE WORD FORMAT & MEL'S TESTLESS LOOP OVERFLOW PROOF
-- =============================================================================

def ADDR_BITS : Nat := 13
def ADDR_MOD  : Nat := 8192   -- 2^13 = 8192 words of drum memory
def OP_MOD    : Nat := 32     -- 5-bit opcode space (0 .. 31)

/-- Structured fields of an RPC-4000 one-plus-one instruction word. -/
structure RPC4000Inst where
  opcode      : Nat
  indexBit    : Nat
  operandAddr : Nat
  nextAddr    : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Encodes `(opcode, indexBit, operandAddr)` into its exact binary arithmetic word value. -/
def encodeCoreWord (opcode indexBit operandAddr : Nat) : Nat :=
  opcode * (2 * ADDR_MOD) + indexBit * ADDR_MOD + operandAddr

/-- Decodes the `operandAddr` field (bits `0..12`). -/
def decodeOperandAddr (word : Nat) : Nat :=
  word % ADDR_MOD

/-- Decodes the `indexBit` field (bit `13`, lying between operand address and opcode). -/
def decodeIndexBit (word : Nat) : Nat :=
  (word / ADDR_MOD) % 2

/-- Decodes the `opcode` field (bits `14..`). -/
def decodeOpcode (word : Nat) : Nat :=
  word / (2 * ADDR_MOD)

/--
  **Theorem 4 (Universal Field Round-Trip):**
  For any valid `opcode`, `indexBit < 2`, and `operandAddr < ADDR_MOD`, decoding
  `encodeCoreWord` recovers all three fields identically.
-/
theorem encode_decode_roundtrip (op idx addr : Nat) (hIdx : idx < 2) (hAddr : addr < ADDR_MOD) :
    decodeOpcode (encodeCoreWord op idx addr) = op ∧
    decodeIndexBit (encodeCoreWord op idx addr) = idx ∧
    decodeOperandAddr (encodeCoreWord op idx addr) = addr := by
  unfold encodeCoreWord decodeOpcode decodeIndexBit decodeOperandAddr ADDR_MOD at *
  have hrem : idx * 8192 + addr < 16384 := by omega
  have hword : op * (2 * 8192) + idx * 8192 + addr = op * 16384 + (idx * 8192 + addr) := by omega
  rw [hword]
  have hop : (op * 16384 + (idx * 8192 + addr)) / 16384 = op := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide)]
    have : (idx * 8192 + addr) / 16384 = 0 := Nat.div_eq_of_lt hrem
    omega
  refine ⟨hop, ?_, ?_⟩
  · have hdiv : (op * 16384 + (idx * 8192 + addr)) / 8192 = op * 2 + idx := by
      have : op * 16384 + (idx * 8192 + addr) = (op * 2 + idx) * 8192 + addr := by omega
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide)]
      have : addr / 8192 = 0 := Nat.div_eq_of_lt hAddr
      omega
    rw [hdiv]
    omega
  · have : op * 16384 + (idx * 8192 + addr) = (op * 2 + idx) * 8192 + addr := by omega
    rw [this, Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hAddr

/--
  **Theorem 5 (Normal Iteration Step — No Overflow While `addr + 1 < ADDR_MOD`):**
  While the operand address has not yet reached the top of memory (`addr + 1 < ADDR_MOD`),
  incrementing the raw instruction word by `1` leaves `opcode` and `indexBit` untouched
  and advances `operandAddr` to `addr + 1`.
-/
theorem mel_loop_normal_increment (op idx addr : Nat) (hIdx : idx < 2) (hAddr : addr + 1 < ADDR_MOD) :
    let w' := encodeCoreWord op idx addr + 1
    decodeOpcode w' = op ∧
    decodeIndexBit w' = idx ∧
    decodeOperandAddr w' = addr + 1 := by
  have : encodeCoreWord op idx addr + 1 = encodeCoreWord op idx (addr + 1) := by
    unfold encodeCoreWord; omega
  dsimp
  rw [this]
  exact encode_decode_roundtrip op idx (addr + 1) hIdx hAddr

/--
  **Theorem 6 (Mel's Carry-Overflow Opcode Mutation Theorem — Universal Proof):**
  When `indexBit = 1` (Mel's "vital clue") and `operandAddr = ADDR_MOD - 1` (the top of memory),
  adding `1` to the raw instruction word:
  1. Mutates `opcode` to `op + 1` (turning the loop instruction into a `JUMP` instruction),
  2. Clears `indexBit` from `1` to `0`, and
  3. Wraps `operandAddr` to `0` (jumping straight to address location `0`)!
-/
theorem mel_carry_overflow_mutates_opcode_to_jump (op : Nat) :
    let w := encodeCoreWord op 1 (ADDR_MOD - 1)
    let w' := w + 1
    decodeOpcode w' = op + 1 ∧
    decodeIndexBit w' = 0 ∧
    decodeOperandAddr w' = 0 := by
  unfold encodeCoreWord decodeOpcode decodeIndexBit decodeOperandAddr ADDR_MOD
  dsimp
  refine ⟨?_, ?_, ?_⟩ <;> omega

-- =============================================================================
-- 5. COMPLETE TESTLESS LOOP MACHINE & TERMINATION PROOF
-- =============================================================================

/-- Example RPC-4000 opcodes: `OP_PROCESS = 10`, and the very next opcode `OP_JUMP = 11`. -/
def OP_PROCESS : Nat := 10
def OP_JUMP    : Nat := 11

/-- State of Mel's self-modifying testless loop. -/
structure MelLoopState where
  instWord  : Nat  -- The self-modifying instruction word held in drum/register
  pc        : Nat  -- Current program counter
  processed : Nat  -- Count of data items processed
  halted    : Bool -- True once control jumps cleanly out to address 0
  deriving Repr, DecidableEq, Inhabited

/--
  One execution cycle of Mel's testless loop:
  - No comparison or conditional branch on the loop index!
  - Only dispatches on the instruction's own opcode (`OP_PROCESS` vs `OP_JUMP`).
  - When `opcode == OP_PROCESS`, processes the datum at `operandAddr` and increments `instWord := instWord + 1`.
  - When `opcode == OP_JUMP`, jumps directly to `pc := operandAddr` (`0`) and exits the loop.
-/
def melLoopStep (st : MelLoopState) : MelLoopState :=
  if st.halted then
    st
  else
    let op := decodeOpcode st.instWord
    let addr := decodeOperandAddr st.instWord
    if op == OP_JUMP then
      { st with pc := addr, halted := true }
    else
      { st with
        instWord  := st.instWord + 1
        processed := st.processed + 1 }

/-- Runs Mel's testless loop for `fuel` steps. -/
def runMelLoop (fuel : Nat) (st : MelLoopState) : MelLoopState :=
  match fuel with
  | 0 => st
  | fuel' + 1 => runMelLoop fuel' (melLoopStep st)

/--
  Initializes Mel's testless loop to process `count` data items located at the top of memory:
  `startAddr = ADDR_MOD - count`, with `opcode = OP_PROCESS` and `indexBit = 1`.
-/
def initMelLoop (count : Nat) : MelLoopState :=
  { instWord  := encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count)
    pc        := 100
    processed := 0
    halted    := false }

/--
  **Theorem 7 (Exact Invariant After `k ≤ count` Steps):**
  For any `count ≤ ADDR_MOD` and any `k ≤ count`, after `k` steps of `runMelLoop`,
  the loop has processed exactly `k` items, has NOT halted yet, and holds
  `instWord = encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count) + k`.
-/
theorem mel_loop_steps_invariant (count : Nat) (hCount : count ≤ ADDR_MOD) (k : Nat) (hk : k ≤ count) :
    runMelLoop k (initMelLoop count) =
      { instWord  := encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count) + k
        pc        := 100
        processed := k
        halted    := false } := by
  induction k with
  | zero =>
    rfl
  | succ k' ih =>
    have hk' : k' ≤ count := by omega
    have hprev := ih hk'
    have hcomm : ∀ (n : Nat) (s : MelLoopState), runMelLoop (n + 1) s = melLoopStep (runMelLoop n s) := by
      intro n
      induction n with
      | zero => intro s; rfl
      | succ n' ihn =>
        intro s
        unfold runMelLoop
        exact ihn (melLoopStep s)
    rw [hcomm k' (initMelLoop count), hprev]
    unfold melLoopStep
    have haddr : (ADDR_MOD - count) + k' < ADDR_MOD := by
      unfold ADDR_MOD at *; omega
    have heq : encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count) + k' =
               encodeCoreWord OP_PROCESS 1 ((ADDR_MOD - count) + k') := by
      unfold encodeCoreWord; omega
    have hOp : decodeOpcode (encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count) + k') = OP_PROCESS := by
      rw [heq]
      exact (encode_decode_roundtrip OP_PROCESS 1 ((ADDR_MOD - count) + k') (by decide) haddr).1
    rw [hOp]
    simp [OP_PROCESS, OP_JUMP]
    omega

/--
  **Theorem 8 (Mel's Testless Loop Terminates Cleanly at Address 0 After Exact `count + 1` Steps):**
  For **any** positive array length `count` (`1 ≤ count ≤ ADDR_MOD`) placed at the top of memory:
  After `count` data-processing iterations, the instruction word overflows its 13-bit address
  through the set index bit (`1`) directly into `OP_JUMP`, and on step `count + 1` control
  exits the testless loop straight to `pc = 0` with `processed = count` and `halted = true`!
-/
theorem mel_testless_loop_exits_to_zero (count : Nat) (hPos : 1 ≤ count) (hBound : count ≤ ADDR_MOD) :
    runMelLoop (count + 1) (initMelLoop count) =
      { instWord  := encodeCoreWord OP_JUMP 0 0
        pc        := 0
        processed := count
        halted    := true } := by
  have hcomm : ∀ (n : Nat) (s : MelLoopState), runMelLoop (n + 1) s = melLoopStep (runMelLoop n s) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n' ihn =>
      intro s
      unfold runMelLoop
      exact ihn (melLoopStep s)
  rw [hcomm count (initMelLoop count)]
  rw [mel_loop_steps_invariant count hBound count (Nat.le_refl count)]
  have hOverflowWord :
      encodeCoreWord OP_PROCESS 1 (ADDR_MOD - count) + count = encodeCoreWord OP_JUMP 0 0 := by
    unfold encodeCoreWord OP_PROCESS OP_JUMP ADDR_MOD at *
    omega
  rw [hOverflowWord]
  unfold melLoopStep
  have hOp : decodeOpcode (encodeCoreWord OP_JUMP 0 0) = OP_JUMP := by
    unfold encodeCoreWord decodeOpcode OP_JUMP ADDR_MOD
    omega
  have hAddr : decodeOperandAddr (encodeCoreWord OP_JUMP 0 0) = 0 := by
    unfold encodeCoreWord decodeOperandAddr OP_JUMP ADDR_MOD
    omega
  simp [hOp, hAddr]

end StoryOfMel