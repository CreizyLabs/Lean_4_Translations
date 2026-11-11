/-!
# Cross-Layer Unification: 1964 Magnetic Amplifier Physics to 1960 Setun ALU
Proves that N. P. Brusentsov's 1964 dual-rail pulse-current magnetic amplifier
half-adder (`Magnetic_Digital_Elements_1964.lean`, Fig. 10, Page 366) is
algebraically isomorphic to the 1960 Setun serial full-adder (`Setun_1960.lean`,
Page 228) with zero carry-in.
Zero `sorry`, zero custom axioms.
-/

import Setun_1960
import Magnetic_Digital_Elements_1964

namespace CrossLayerBridge

open Setun1960
open MagneticDigitalElements1964

/-- Encodes a Setun-1960 `Trit` into its physical 1964 dual-rail magnetic amplifier
    representation `(pos_rail, neg_rail) ∈ {(0, 0), (1, 0), (0, 1)}`. -/
def tritToDualRail : Trit → Int × Int
  | .neg  => (0, 1)
  | .zero => (0, 0)
  | .pos  => (1, 0)

/-- The physical dual-rail difference `pos_rail - neg_rail` recovers the exact integer
    value `t.toInt ∈ {-1, 0, +1}` of any Setun `Trit`. -/
theorem tritToDualRail_diff (t : Trit) :
    let (p, n) := tritToDualRail t
    p - n = t.toInt := by
  cases t <;> rfl

/-- Cross-Epoch Hardware Equivalence Theorem:
    For all 9 combinations of balanced ternary trits `a, b : Trit`, feeding their
    dual-rail pulse-current signals into Brusentsov's 1964 magnetic amplifier
    half-adder (`brusentsovHalfAdder`) produces the exact same `(sum, carry_out)`
    pair as the 1960 Setun serial full-adder (`Trit.fullAdder a b .zero`). -/
theorem brusentsov_1964_half_adder_eq_setun_1960_adder (a b : Trit) :
    let (ap, an) := tritToDualRail a
    let (bp, bn) := tritToDualRail b
    let (S_1964, Q_1964) := brusentsovHalfAdder ap an bp bn
    let (S_1960, Q_1960) := Trit.fullAdder a b .zero
    S_1964 = S_1960.toInt ∧ Q_1964 = Q_1960.toInt := by
  cases a <;> cases b <;> decide

end CrossLayerBridge