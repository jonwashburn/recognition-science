import Mathlib
import RecognitionScience.Cost
import RecognitionScience.Foundation.LawOfExistence

/-!
# Dimensional Constraints: Cost Layer

This file packages the public cost-theoretic core used in the dimensional
constraints rebuttal.

It exposes the statements needed in the paper in a compact, paper-specific
namespace without importing confidential parts of the full development.
-/

namespace RecognitionScience
namespace Papers
namespace DimensionalConstraints
namespace CostLayer

open Real

/-- Public cost layer used in the dimensional-constraints rebuttal. -/
structure PublicCostLayer : Prop where
  /-- Any admissible cost functional agrees with `Jcost` on positive reals. -/
  unique_on_pos :
    ∀ (F : ℝ → ℝ) [Cost.JensenSketch F] {x : ℝ},
      0 < x → F x = Cost.Jcost x
  /-- In logarithmic coordinates, the cost is `cosh t - 1`. -/
  log_closed_form :
    ∀ t : ℝ, Cost.Jlog t = Real.cosh t - 1
  /-- The identity ratio has zero cost. -/
  normalized : Cost.Jcost 1 = 0
  /-- Reciprocal ratios have equal cost. -/
  reciprocal :
    ∀ {x : ℝ}, 0 < x → Cost.Jcost x = Cost.Jcost x⁻¹
  /-- The cost is nonnegative on positive ratios. -/
  nonnegative :
    ∀ {x : ℝ}, 0 < x → 0 ≤ Cost.Jcost x
  /-- The unique positive zero of the cost is `x = 1`. -/
  zero_iff_one :
    ∀ {x : ℝ}, 0 < x → (Cost.Jcost x = 0 ↔ x = 1)
  /-- Near zero, the defect exceeds every prescribed bound. -/
  null_barrier :
    ∀ C : ℝ, ∃ ε > 0, ∀ x : ℝ, 0 < x → x < ε →
      C < Foundation.LawOfExistence.defect x

/-- The public cost layer is available in the current public framework. -/
theorem public_cost_layer : PublicCostLayer := by
  refine
    { unique_on_pos := ?_
      log_closed_form := Cost.Jlog_as_cosh
      normalized := Cost.Jcost_unit0
      reciprocal := ?_
      nonnegative := ?_
      zero_iff_one := ?_
      null_barrier := Foundation.LawOfExistence.nothing_cannot_exist }
  · intro F _ x hx
    exact @Cost.T5_cost_uniqueness_on_pos F _ x hx
  · intro x hx
    exact Cost.Jcost_symm hx
  · intro x hx
    exact Cost.Jcost_nonneg hx
  · intro x hx
    exact Cost.Jcost_eq_zero_iff x hx

end CostLayer
end DimensionalConstraints
end Papers
end RecognitionScience
