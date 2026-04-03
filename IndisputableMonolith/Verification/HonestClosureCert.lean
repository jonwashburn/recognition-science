import Mathlib
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.RSCompliance
import IndisputableMonolith.Constants

/-!
# Honest Closure Certificate

This certificate provides **honest framing** of what the Recognition Science
matching certificates actually prove, distinguishing:

- `dimlessPack_explicit` = **legacy/audit** evaluator (ignores L/B)
- `dimlessPack_fromStructure` = **certified structural** evaluator (reads from structure)

## What IS Certified

1. **φ-closure**: All legacy observable formulas are algebraic in φ.
2. **Structural predicates**: K-gate, eight-tick, Born rule are PROVEN.
3. **Calibration uniqueness**: Every ledger/bridge has unique calibration.
4. **Structural derivation**: `dimlessPack_fromStructure` reads mass ratios
   from ledger torsion, mixing from bridge geometry, g-2 from loop order.
5. For the canonical RS-compliant pair, derived alpha equals the φ-formula.

## Legacy surface

`dimlessPack_explicit` still ignores its Ledger/Bridge arguments.
This is preserved intentionally as an audit surface.
-/

namespace IndisputableMonolith
namespace Verification
namespace HonestClosure

open IndisputableMonolith.RecogSpec
open IndisputableMonolith.Constants

structure HonestClosureCert where
  deriving Repr

@[simp] def HonestClosureCert.verified (_c : HonestClosureCert) : Prop :=
  -- Part A: Legacy observables are φ-closed
  (∀ φ, PhiClosed φ (alphaDefault φ)) ∧
  (∀ φ, (massRatiosDefault φ).Forall (PhiClosed φ)) ∧
  (∀ φ, (mixingAnglesDefault φ).Forall (PhiClosed φ)) ∧
  (∀ φ, PhiClosed φ (g2Default φ)) ∧
  -- Part B: Structural predicates are proven
  kGateWitness ∧
  eightTickWitness ∧
  bornHolds ∧
  -- Part C: Calibration uniqueness
  (∀ (L : Ledger) (B : Bridge L) (A : Anchors), UniqueCalibration L B A) ∧
  -- Part D: Legacy α matches constant
  (alphaDefault phi = alphaLock) ∧
  -- Part E (NEW): Structural evaluator uses its arguments
  (∀ (L : RSLedger) (B : RSBridge L),
    (dimlessPack_fromStructure phi L B).alpha = B.alphaExponent) ∧
  (∀ (L : RSLedger) (B : RSBridge L),
    (dimlessPack_fromStructure phi L B).massRatios = massRatiosFromTiers L phi) ∧
  -- Part F (NEW): Canonical RS-compliant pair has structural agreement
  RSCompliant phi canonicalRSLedger (canonicalRSBridge canonicalRSLedger)

@[simp] theorem HonestClosureCert.verified_any (c : HonestClosureCert) :
    HonestClosureCert.verified c := by
  refine ⟨?phiA, ?phiM, ?phiMix, ?phiG2, ?kgate, ?tick, ?born, ?calib, ?alphaEq,
          ?structAlpha, ?structMass, ?compliant⟩
  · intro φ; exact phiClosed_alphaDefault φ
  · intro φ
    simp only [LeptonMassRatios.Forall, massRatiosDefault]
    exact ⟨PhiClosed.self _, phiClosed_one_div_pow _ 2, phiClosed_one_div _⟩
  · intro φ
    simp only [CkmMixingAngles.Forall, mixingAnglesDefault]
    exact ⟨phiClosed_one_div _, phiClosed_one_div_pow _ 2, phiClosed_one_div_pow _ 3⟩
  · intro φ; exact phiClosed_one_div_pow φ 5
  · exact kGate_from_units
  · exact eightTick_from_TruthCore
  · exact born_from_TruthCore
  · intro L B A; exact uniqueCalibration_any L B A
  · rfl
  · intro L B; exact derivation_uses_structure_alpha L B
  · intro L B; exact derivation_uses_structure_mass L B
  · exact canonical_is_compliant

/-- The LEGACY evaluator ignores its Ledger/Bridge arguments.
    Preserved as audit surface. -/
theorem legacy_evaluator_ignores_structure :
    ∀ (φ : ℝ) (L₁ L₂ : Ledger) (B₁ : Bridge L₁) (B₂ : Bridge L₂),
      (dimlessPack_explicit φ L₁ B₁).alpha = (dimlessPack_explicit φ L₂ B₂).alpha ∧
      (dimlessPack_explicit φ L₁ B₁).massRatios = (dimlessPack_explicit φ L₂ B₂).massRatios ∧
      (dimlessPack_explicit φ L₁ B₁).mixingAngles = (dimlessPack_explicit φ L₂ B₂).mixingAngles ∧
      (dimlessPack_explicit φ L₁ B₁).g2Muon = (dimlessPack_explicit φ L₂ B₂).g2Muon := by
  intro φ L₁ L₂ B₁ B₂
  simp [dimlessPack_explicit]

end HonestClosure
end Verification
end IndisputableMonolith
