/-
  BkjckTape.lean
  Exact, Total, Peer-Review-Grade Lean 4 Translation & Checksum Verification
  of Mel Kaye's LGP-30 Blackjack Machine-Code Tape (`bkjck.tx.txt`).

  Contains all 10 tracks (Tracks 45..54, 640 32-bit LGP-30 words) verbatim with exact
  29-bit LGP-30 paper-tape checksum verification proved at compile time by the Lean 4 kernel.

  Guarantees:
  - Zero `sorry`
  - Zero custom `axiom`
  - Zero `partial` or `unsafe` functions
  - Zero approximations
-/

namespace BkjckTape

-- =============================================================================
-- 1. LGP-30 TAPE TRACK STRUCTURE & 29-BIT CHECKSUM ENGINE
-- =============================================================================

/-- Exact representation of one 64-word LGP-30 drum track from `bkjck.tx`. -/
structure TapeTrack where
  header   : UInt32
  trackNum : Nat
  checksum : UInt32
  words    : Array UInt32
  deriving Repr, DecidableEq, Inhabited

/--
  Exact 29-bit LGP-30 track checksum accumulator (sign bit unprotected to prevent
  30-bit arithmetic overflow, matching `mel.c` `load_track`):
    c += w & 0x7ffffffe;
    c += c >> 29;
    c &= 0x3ffffffe;
-/
@[inline] def checksumStep (c w : UInt32) : UInt32 :=
  let c1 := c + (w &&& 0x7ffffffe)
  let c2 := c1 + (c1 >>> 29)
  c2 &&& 0x3ffffffe

/-- Computes the exact 29-bit LGP-30 checksum over an array of 32-bit words. -/
def computeTrackChecksum (words : Array UInt32) : UInt32 :=
  words.toList.foldl checksumStep 0

/-- Validates that a `TapeTrack` has 64 words, matching header track number, and exact 29-bit checksum. -/
def verifyTrack (t : TapeTrack) : Bool :=
  (t.words.size == 64) &&
  (((t.header >>> 8) &&& 0x3f).toNat == t.trackNum) &&
  ((computeTrackChecksum t.words ^^^ t.checksum) == 0)

-- =============================================================================
-- 2. ALL 10 VERBATIM TRACKS OF MEL KAYE'S BLACKJACK TAPE (`bkjck.tx.txt`)
-- =============================================================================

/-- Track 45 (LGP-30 header `0x00402d00`, 29-bit checksum `0x3c6fc54c`). -/
def track45 : TapeTrack := {
  header := 0x00402d00
  trackNum := 45
  checksum := 0x3c6fc54c
  words := #[
    0x000d2f8c, 0x000d3278, 0x000a31c4, 0x000e2d98, 0x00022d78, 0x000e2efc, 0x00022d54, 0x00022d58,
    0x00022d6c, 0x000332f0, 0x000a32d8, 0x000931f0, 0x000f31e0, 0x000b2d24, 0x000e2e8c, 0x000c2d94,
    0x000e2d0c, 0x00022d68, 0x00022d70, 0x00022d50, 0x00012da8, 0x00092de4, 0x000f2de4, 0x000b2d68,
    0x000a2e68, 0x00012dd0, 0x00012da8, 0x000e2de4, 0x000c2da8, 0x000d2d88, 0x00012dd4, 0x000d2d8c,
    0x00033300, 0x000a3300, 0x56a40656, 0x0e06627e, 0x000a2e00, 0x00000018, 0x00002dd0, 0x11f20806,
    0x56140656, 0x561c0656, 0x56a40656, 0x572c0656, 0x56340656, 0x563c0656, 0x56440656, 0x564c0656,
    0x280c0406, 0x10640806, 0x10750806, 0x106c0806, 0x0e067a7e, 0x0e06627e, 0x0e062a7e, 0x0e066a7e,
    0x01000000, 0x00800000, 0x00010000, 0x00008000, 0x80000004, 0x7e7e7e7e, 0x7ffffffc, 0x00400000
  ]
}

/-- Track 46 (LGP-30 header `0x00402e00`, 29-bit checksum `0x2216f45e`). -/
def track46 : TapeTrack := {
  header := 0x00402e00
  trackNum := 46
  checksum := 0x2216f45e
  words := #[
    0x00012d94, 0x000f31fc, 0x000b2e24, 0x000f329c, 0x000b2e1c, 0x00012fc4, 0x000a2e28, 0x00012d94,
    0x000a2e28, 0x00012df0, 0x000a2fe0, 0x00012e78, 0x00022e38, 0x00022e40, 0x00012dd0, 0x00092df4,
    0x000d2dd0, 0x00012e38, 0x000e2e8c, 0x000c2e38, 0x00022e40, 0x000f2d64, 0x000b2e38, 0x000d2f8c,
    0x000d2f8c, 0x000a2e88, 0x000332f0, 0x000a32cc, 0x000931e0, 0x000a2d0c, 0x00002d9c, 0x000131d4,
    0x000f2f8c, 0x800b2e2c, 0x00081000, 0x00000004, 0x00081800, 0x00032e28, 0x000a2e68, 0x000d33b4,
    0x00080c00, 0x00000058, 0x00081800, 0x00032e28, 0x000a2e68, 0x000d3274, 0x00033300, 0x000a3300,
    0x20187e7e, 0x00081800, 0x0001327c, 0x000e2e8c, 0x000d327c, 0x000a2ed8, 0x00032e28, 0x000a2e68,
    0x000b2f2c, 0x000e33b4, 0x000c33b4, 0x00092df8, 0x000f2ea4, 0x000b2f60, 0x00080c00, 0x00000010
  ]
}

/-- Track 47 (LGP-30 header `0x00402f00`, 29-bit checksum `0x3a4f87fa`). -/
def track47 : TapeTrack := {
  header := 0x00402f00
  trackNum := 47
  checksum := 0x3a4f87fa
  words := #[
    0x00081800, 0x00012f5c, 0x000e2e8c, 0x000d2f5c, 0x00032e28, 0x000a2e68, 0x000b2f3c, 0x000e3274,
    0x000c3274, 0x000b3068, 0x000a2ff8, 0x000133b4, 0x00092df8, 0x000e2df0, 0x000a2ee8, 0x00013274,
    0x00092df8, 0x000e2df0, 0x000a2f20, 0x00013274, 0x00092df8, 0x000e2df0, 0x000a2fe8, 0x00000000,
    0x00033300, 0x000a3300, 0x20106a08, 0x721a2a10, 0x2608067e, 0x00080000, 0x00040000, 0x00092efc,
    0x000f2efc, 0x000b2f90, 0x000a2ec4, 0x00002d9c, 0x00081800, 0x00000030, 0x000133b4, 0x000b2fa4,
    0x000a2fc0, 0x00092df8, 0x000c33b4, 0x000f2f94, 0x000b2fb8, 0x000a2fc0, 0x000e2ea4, 0x000d33b4,
    0x00080c00, 0x00000028, 0x00081800, 0x00012f5c, 0x000e2e8c, 0x000d2f5c, 0x00032e28, 0x000a2e68,
    0x000b2f4c, 0x000e3274, 0x000c3274, 0x00092df8, 0x000f2ea4, 0x000b3004, 0x00080c00, 0x000133b4
  ]
}

/-- Track 48 (LGP-30 header `0x00403000`, 29-bit checksum `0x07e49bdc`). -/
def track48 : TapeTrack := {
  header := 0x00403000
  trackNum := 48
  checksum := 0x07e49bdc
  words := #[
    0x000a3074, 0x000e2efc, 0x000b3010, 0x000a2ff8, 0x000e2e8c, 0x000b303c, 0x000332f0, 0x000a32d8,
    0x00092f94, 0x000f2f94, 0x000b2ff8, 0x00081000, 0x00000014, 0x00081800, 0x000a2fc4, 0x000e3030,
    0x000b304c, 0x000a302c, 0x211b589a, 0x000e2efc, 0x000b302c, 0x00013274, 0x000b3060, 0x000a302c,
    0x000e2fc4, 0x000a2fe8, 0x000e2fc4, 0x000d3274, 0x000a2ff8, 0x00092df8, 0x000c33b4, 0x000f2ea4,
    0x000b30a0, 0x00033300, 0x000a3300, 0x20300a52, 0x7a5a7e7e, 0x000d33b4, 0x000d33b4, 0x000a3130,
    0x000e2e8c, 0x000b30d4, 0x00012e8c, 0x000f327c, 0x000b30d4, 0x00033300, 0x000a3300, 0x20300a0c,
    0x726a6c64, 0x726a6c7e, 0x00012e78, 0x000d2f8c, 0x000a30f4, 0x0001327c, 0x000f2efc, 0x000b3110,
    0x00033300, 0x000a3300, 0x20302c06, 0x6a721a2a, 0x7a7e7e7e, 0x00012ea4, 0x000d33b4, 0x00013278
  ]
}

/-- Track 49 (LGP-30 header `0x00403100`, 29-bit checksum `0x19cd56c2`). -/
def track49 : TapeTrack := {
  header := 0x00403100
  trackNum := 49
  checksum := 0x19cd56c2
  words := #[
    0x000e2e8c, 0x000d3278, 0x000a3130, 0x00000100, 0x00033300, 0x000a3300, 0x20305a46, 0x5a720c06,
    0x0e067e7e, 0x000133b4, 0x000332b8, 0x000a3280, 0x00013274, 0x00092df8, 0x000c3274, 0x000f2ea4,
    0x000b3204, 0x00033300, 0x000a3300, 0x30180a52, 0x7a5a1806, 0x0606067e, 0x000d3274, 0x000d3274,
    0x00013274, 0x000f33b4, 0x000b3268, 0x00013278, 0x000f2e8c, 0x000d3278, 0x00033300, 0x000a3300,
    0x307a6a46, 0x1a4a0610, 0x1608067e, 0x00013278, 0x000b31dc, 0x000c2d94, 0x00033300, 0x000a3300,
    0x1034087e, 0x00012d94, 0x000332b8, 0x000a3280, 0x00033300, 0x000a3300, 0x2e04047e, 0x00013278,
    0x000b31f8, 0x00081000, 0x000d327c, 0x000d327c, 0x000d2f5c, 0x00000068, 0x000a32f4, 0x00080c00,
    0x0000000c, 0x000d3278, 0x000f3278, 0x00080700, 0x0000003c, 0x000a3194, 0x00080c00, 0x00000008
  ]
}

/-- Track 50 (LGP-30 header `0x00403200`, 29-bit checksum `0x2f60d030`). -/
def track50 : TapeTrack := {
  header := 0x00403200
  trackNum := 50
  checksum := 0x2f60d030
  words := #[
    0x000a31c4, 0x000e2e8c, 0x000b3240, 0x00012e8c, 0x000f2f5c, 0x000b3240, 0x00033300, 0x000a3300,
    0x30180a0c, 0x726a6c64, 0x726a6c7e, 0x00080c00, 0x000133b4, 0x000f2ea4, 0x000b33f4, 0x000a33e8,
    0x00033300, 0x000a3300, 0x30185a46, 0x5a720c06, 0x0e067e7e, 0x00013274, 0x000332b8, 0x000a3280,
    0x00080c00, 0x000a3160, 0x00013278, 0x000e2e8c, 0x000a3174, 0x00000050, 0xffffffe8, 0x00000000,
    0x000f2fc4, 0x000b32a0, 0x000f2fc4, 0x000b32bc, 0x000f2fc4, 0x000b32c4, 0x00080e00, 0x00000024,
    0x000e2fc4, 0x0006310c, 0x000e32b4, 0x000232b0, 0x00081a00, 0x00000200, 0x000a31b0, 0x00080600,
    0x000a329c, 0x00080a00, 0x000a329c, 0x00012f8c, 0x000e2e8c, 0x000d2f8c, 0x00013048, 0x00063048,
    0x000c3048, 0x00072e64, 0x000e3048, 0x000c3048, 0x000a2d2c, 0x00000400, 0x00081000, 0x000a2e78
  ]
}

/-- Track 51 (LGP-30 header `0x00403300`, 29-bit checksum `0x00e0c242`). -/
def track51 : TapeTrack := {
  header := 0x00403300
  trackNum := 51
  checksum := 0x00e0c242
  words := #[
    0x000131bc, 0x000933b0, 0x000a330c, 0x000f339c, 0x000b3350, 0x000a3344, 0x7e000000, 0x047e0000,
    0x00004000, 0x00003f00, 0x00080068, 0x0000000c, 0x00000004, 0x00000004, 0x00013300, 0x000e33cc,
    0x000a33a8, 0x000133cc, 0x000e3300, 0x000a33e0, 0x000e3318, 0x000c331c, 0x00073320, 0x00093324,
    0x000e3328, 0x000d33bc, 0x000a3338, 0x000e3318, 0x000c331c, 0x00073320, 0x00093324, 0x000e3328,
    0x000d33bc, 0x000f3330, 0x000e3334, 0x00000000, 0x000b3300, 0x000a33bc, 0x00000100, 0x7e000000,
    0x00013300, 0x000a33e0, 0x00023300, 0x000a33b8, 0x7e7e7e7e, 0x0000004c, 0x0001332c, 0x00080268,
    0x000c3334, 0x0001331c, 0x000a33d0, 0x00000004, 0x00063398, 0x000f339c, 0x000b336c, 0x000a339c,
    0x000233e4, 0x000a31bc, 0x00013278, 0x000f2e8c, 0x000d3278, 0x00012e78, 0x000d2f8c, 0x000a316c
  ]
}

/-- Track 52 (LGP-30 header `0x00403400`, 29-bit checksum `0x00000000`). -/
def track52 : TapeTrack := {
  header := 0x00403400
  trackNum := 52
  checksum := 0x00000000
  words := mkArray 64 0
}

/-- Track 53 (LGP-30 header `0x00403500`, 29-bit checksum `0x00000000`). -/
def track53 : TapeTrack := {
  header := 0x00403500
  trackNum := 53
  checksum := 0x00000000
  words := mkArray 64 0
}

/-- Track 54 (LGP-30 header `0x00403600`, 29-bit checksum `0x00000000`). -/
def track54 : TapeTrack := {
  header := 0x00403600
  trackNum := 54
  checksum := 0x00000000
  words := mkArray 64 0
}

/-- Complete list of all 10 tracks (Tracks 45 through 54) from `bkjck.tx.txt`. -/
def allTracks : List TapeTrack := [
  track45, track46, track47, track48, track49,
  track50, track51, track52, track53, track54
]

/-- Loads all 10 tracks of `bkjck.tx` directly into a 4096-word LGP-30 drum memory image. -/
def loadDrumImage : Array UInt32 :=
  allTracks.foldl (fun mem t =>
    let base := 64 * t.trackNum
    let rec writeWords (i : Nat) (acc : Array UInt32) : Array UInt32 :=
      match i with
      | 0 => acc
      | i' + 1 =>
        let acc' := writeWords i' acc
        acc'.setIfInBounds (base + i') (t.words.getD i' 0)
    writeWords t.words.size mem
  ) (mkArray 4096 0)

-- =============================================================================
-- 3. MACHINE-CHECKED KERNEL VERIFICATION THEOREMS (ALL 10 TRACKS)
-- =============================================================================

set_option maxRecDepth 200000

/-- Theorem 1: Track 45 (entry track `0402k00'`) has 64 words and passes its 29-bit checksum. -/
theorem track45_checksum_verified : verifyTrack track45 = true := rfl

/-- Theorem 2: Track 46 (`0402q00'`) has 64 words and passes its 29-bit checksum. -/
theorem track46_checksum_verified : verifyTrack track46 = true := rfl

/-- Theorem 3: Track 47 (`0402w00'`) has 64 words and passes its 29-bit checksum. -/
theorem track47_checksum_verified : verifyTrack track47 = true := rfl

/-- Theorem 4: Track 48 (`0403000'`) has 64 words and passes its 29-bit checksum. -/
theorem track48_checksum_verified : verifyTrack track48 = true := rfl

/-- Theorem 5: Track 49 (`0403l00'`) has 64 words and passes its 29-bit checksum. -/
theorem track49_checksum_verified : verifyTrack track49 = true := rfl

/-- Theorem 6: Track 50 (`0403200'`) has 64 words and passes its 29-bit checksum. -/
theorem track50_checksum_verified : verifyTrack track50 = true := rfl

/-- Theorem 7: Track 51 (`0403300'`) has 64 words and passes its 29-bit checksum. -/
theorem track51_checksum_verified : verifyTrack track51 = true := rfl

/-- Theorem 8: Tracks 52, 53, and 54 (working data tracks) are zero-initialized and pass checksums. -/
theorem tracks52_to_54_checksum_verified :
    verifyTrack track52 = true ∧ verifyTrack track53 = true ∧ verifyTrack track54 = true :=
  ⟨rfl, rfl, rfl⟩

/--
  **Main Tape Integrity Theorem:**
  Every single one of the 10 tracks (640 32-bit machine words) of Mel Kaye's `bkjck.tx`
  passes its exact 29-bit LGP-30 checksum with zero errors.
-/
theorem bkjck_full_tape_verified :
    allTracks.length = 10 ∧
    allTracks.all verifyTrack = true :=
  ⟨rfl, rfl⟩

end BkjckTape