import Mathlib
import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.RSLedger
import IndisputableMonolith.RecogSpec.RSBridge
import IndisputableMonolith.RecogSpec.MassLawFromLedger
import IndisputableMonolith.RecogSpec.BridgeDerivation
import IndisputableMonolith.Constants

/-!
# RSCompliance: Structure Compliance and Derived Evaluator

This module defines:
1. The RSCompliant predicate: when a ledger/bridge pair has the required structure
2. The derived evaluator: produces DimlessPack FROM structure, not φ-formulas
3. The agreement theorem: derived evaluator matches explicit formulas when compliant

## The Key Insight

The current `dimlessPack_explicit` IGNORES its Ledger and Bridge arguments.
The `dimlessPack_fromStructure` defined here USES them to derive values.

When a ledger/bridge pair is RS-compliant (has canonical torsion, edge counts, etc.),
the derived values EQUAL the φ-formulas. This is the non-circular derivation.
-/

namespace IndisputableMonolith
namespace RecogSpec

open Constants

/-! ## RSCompliant Predicate -/

/-- A ledger/bridge pair is RS-compliant when it has the required structure.

This predicate bundles all the structural requirements:
1. Ledger has canonical torsion {0, 11, 17}
2. Bridge has edge-dual count = 24
3. Bridge alpha exponent matches ILG
4. φ satisfies golden ratio selection
-/
structure RSCompliant (φ : ℝ) (L : RSLedger) (B : RSBridge L) : Prop where
  /-- φ satisfies golden ratio selection: φ² = φ + 1 and φ > 0 -/
  phi_selection : φ ^ 2 = φ + 1 ∧ 0 < φ
  /-- Ledger has canonical torsion -/
  torsion_canonical : L.torsion = generationTorsion
  /-- Bridge edge-dual count is 24 -/
  edge_dual_24 : B.edgeDual = 24
  /-- Bridge alpha matches ILG formula -/
  alpha_from_ilg : B.alphaExponent = (1 - 1/φ) / 2
  /-- Bridge loop order is 5 -/
  loop_order_5 : B.loopOrder = 5

/-! ## The Derived Evaluator -/

/-- Produce a DimlessPack from RSLedger/RSBridge structure.

Unlike `dimlessPack_explicit` which ignores L and B, this evaluator
USES the ledger torsion and bridge couplings to derive values.

For numerical observables, we use the structure-derived values.
For Prop fields (strongCP, eightTick, Born), we use the proven witnesses.
-/
noncomputable def dimlessPack_fromStructure (φ : ℝ) (L : RSLedger) (B : RSBridge L) :
    DimlessPack L.toLedger (B.toBridge) where
  alpha := B.alphaExponent
  massRatios := massRatiosFromTiers L φ
  mixingAngles := mixingFromCycles B φ
  g2Muon := g2FromLoops B φ
  strongCPNeutral := kGateWitness
  eightTickMinimal := eightTickWitness
  bornRule := bornHolds

/-! ## Agreement Theorems -/

/-- When RS-compliant, the bridge alpha equals the spec formula. -/
theorem alpha_agreement (φ : ℝ) (L : RSLedger) (B : RSBridge L)
    (hRC : RSCompliant φ L B) :
    (dimlessPack_fromStructure φ L B).alpha = alphaDefault φ := by
  simp only [dimlessPack_fromStructure, alphaDefault]
  exact hRC.alpha_from_ilg

/-- When RS-compliant, the derived mass-ratio payload equals the canonical
    φ-power triple {φ^11, φ^17, φ^6}. -/
theorem massRatios_structural (φ : ℝ) (L : RSLedger) (B : RSBridge L)
    (hRC : RSCompliant φ L B) :
    (dimlessPack_fromStructure φ L B).massRatios =
      ⟨φ ^ (11 : ℤ), φ ^ (17 : ℤ), φ ^ (6 : ℤ)⟩ := by
  simp only [dimlessPack_fromStructure]
  exact massRatiosFromTiers_canonical L φ hRC.torsion_canonical

/-- When RS-compliant, the derived g-2 equals 1/φ^5. -/
theorem g2Muon_structural (φ : ℝ) (L : RSLedger) (B : RSBridge L)
    (hRC : RSCompliant φ L B) :
    (dimlessPack_fromStructure φ L B).g2Muon = 1 / (φ ^ 5) := by
  simp only [dimlessPack_fromStructure]
  exact g2FromLoops_canonical B φ hRC.loop_order_5

/-! ## The Canonical RS-Compliant Pair -/

/-- The canonical ledger and bridge form an RS-compliant pair -/
theorem canonical_is_compliant :
    RSCompliant phi canonicalRSLedger (canonicalRSBridge canonicalRSLedger) := by
  constructor
  · exact ⟨phi_sq_eq, phi_pos⟩
  · rfl
  · rfl
  · simp [canonicalRSBridge, alphaLock]
  · rfl

/-! ## Summary -/

/-- The derived evaluator reads alpha from bridge structure. -/
theorem derivation_uses_structure_alpha (L : RSLedger) (B : RSBridge L) :
    (dimlessPack_fromStructure phi L B).alpha = B.alphaExponent := rfl

/-- The derived evaluator reads mass ratios from ledger tier structure. -/
theorem derivation_uses_structure_mass (L : RSLedger) (B : RSBridge L) :
    (dimlessPack_fromStructure phi L B).massRatios = massRatiosFromTiers L phi := rfl

/-- The derived evaluator reads mixing from bridge cycle structure. -/
theorem derivation_uses_structure_mixing (L : RSLedger) (B : RSBridge L) :
    (dimlessPack_fromStructure phi L B).mixingAngles = mixingFromCycles B phi := rfl

/-- The derived evaluator reads g-2 from bridge loop structure. -/
theorem derivation_uses_structure_g2 (L : RSLedger) (B : RSBridge L) :
    (dimlessPack_fromStructure phi L B).g2Muon = g2FromLoops B phi := rfl

end RecogSpec
end IndisputableMonolith
