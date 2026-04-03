import Mathlib
import RecognitionScience.Foundation.LedgerCanonicality
import RecognitionScience.Foundation.HierarchyEmergence

namespace RecognitionScience
namespace Foundation
namespace HierarchyForcing

open LedgerCanonicality
open HierarchyEmergence

/-!
# Gap 2: Nontrivial Zero-Parameter Ledger → Hierarchical Structure (H1 Forced)

Phase 3 of the axiom-closure plan.

Two theorems, zero axioms:
1. Uniform scaling is forced by the no-free-knobs condition.
2. Additive composition (a=b=1) is the unique minimizer of max(a,b)
   among positive-integer recurrence coefficients.
-/

/-- Multilevel composition with at least three levels. -/
structure NontrivialMultilevelComposition where
  levels : ℕ → ℝ
  levels_pos : ∀ k, 0 < levels k
  at_least_three : 0 < levels 0 ∧ 0 < levels 1 ∧ 0 < levels 2

/-- **Theorem**: No free scale parameters forces uniform adjacent ratios. -/
theorem uniform_scaling_forced
    (M : NontrivialMultilevelComposition)
    (no_free_scale : ∀ j k,
      M.levels (j + 1) / M.levels j = M.levels (k + 1) / M.levels k)
    (ratio_gt_one : 1 < M.levels 1 / M.levels 0) :
    ∃ σ : ℝ, 1 < σ ∧ ∀ k, M.levels (k + 1) = σ * M.levels k := by
  use M.levels 1 / M.levels 0
  refine ⟨ratio_gt_one, fun k => ?_⟩
  have hk := M.levels_pos k
  have h0 := M.levels_pos 0
  have hratio := no_free_scale k 0
  rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt h0)] at hratio
  have : M.levels (k + 1) = M.levels 1 / M.levels 0 * M.levels k := by
    field_simp; linarith
  exact this

/-- **Theorem (Phase 3)**: Among recurrence coefficients (a, b) with
a ≥ 1 and b ≥ 1, the pair (1, 1) uniquely minimizes max(a, b).
No axiom needed — this is pure arithmetic. -/
theorem additive_composition_is_minimal (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b = 1 → a = 1 ∧ b = 1 := by
  intro h
  constructor
  · exact Nat.le_antisymm (by omega) ha
  · exact Nat.le_antisymm (by omega) hb

/-- The pair (1,1) achieves max = 1. -/
theorem min_max_achieved : max 1 1 = 1 := by simp

/-- Any other pair has max ≥ 2. -/
theorem other_pairs_larger (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ¬(a = 1 ∧ b = 1)) : 2 ≤ max a b := by omega

/-- Construct the uniform scale ladder from forced data. -/
noncomputable def hierarchy_forced
    (M : NontrivialMultilevelComposition)
    (no_free_scale : ∀ j k,
      M.levels (j + 1) / M.levels j = M.levels (k + 1) / M.levels k)
    (ratio_gt_one : 1 < M.levels 1 / M.levels 0) :
    UniformScaleLadder :=
  { levels := M.levels
    levels_pos := M.levels_pos
    ratio := M.levels 1 / M.levels 0
    ratio_gt_one := ratio_gt_one
    uniform_scaling := fun k => by
      have hk := M.levels_pos k
      have h0 := M.levels_pos 0
      have hratio := no_free_scale k 0
      rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt h0)] at hratio
      field_simp; linarith }

/-- The forced hierarchy yields σ = φ. -/
theorem hierarchy_forced_gives_phi
    (M : NontrivialMultilevelComposition)
    (no_free_scale : ∀ j k,
      M.levels (j + 1) / M.levels j = M.levels (k + 1) / M.levels k)
    (ratio_gt_one : 1 < M.levels 1 / M.levels 0)
    (additive : M.levels 2 = M.levels 1 + M.levels 0) :
    (hierarchy_forced M no_free_scale ratio_gt_one).ratio = PhiForcing.φ :=
  hierarchy_emergence_forces_phi
    (hierarchy_forced M no_free_scale ratio_gt_one)
    additive

end HierarchyForcing
end Foundation
end RecognitionScience
