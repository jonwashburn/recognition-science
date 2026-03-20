import Mathlib
import RecognitionScience.Foundation.DimensionalConstraints.CostLayer
import RecognitionScience.Foundation.DimensionalConstraints.ContinuumLayer
import RecognitionScience.Foundation.DimensionalConstraints.DimensionLayer

/-!
# Dimensional Constraints: Public Core

This file bundles the paper-specific public formalization used by the
dimensional constraints rebuttal.

It is intentionally small: it exposes only the public cost, continuum, and
dimension layers needed for the paper-facing argument.
-/

namespace RecognitionScience
namespace Foundation
namespace DimensionalConstraints
namespace Core

/-- The bundled public core for the dimensional-constraints paper. -/
structure PublicCore : Prop where
  cost : CostLayer.PublicCostLayer
  continuum : ContinuumLayer.PublicContinuumLayer
  dimension : DimensionLayer.PublicDimensionLayer

/-- The public dimensional-constraints core is available. -/
theorem public_core : PublicCore := by
  exact
    { cost := CostLayer.public_cost_layer
      continuum := ContinuumLayer.public_continuum_layer
      dimension := DimensionLayer.public_dimension_layer }

/-- Compact corollary: the public core pins the compatible dimension to `3`. -/
theorem dimension_three_is_forced :
    (∃! D : Foundation.DimensionForcing.Dimension,
      Foundation.DimensionForcing.RSCompatibleDimension D) ∧
    (∀ D : Foundation.DimensionForcing.Dimension,
      Foundation.DimensionForcing.RSCompatibleDimension D → D = 3) := by
  refine ⟨public_core.dimension.unique_dimension, ?_⟩
  intro D hD
  exact public_core.dimension.compatible_implies_three D hD

end Core
end DimensionalConstraints
end Foundation
end RecognitionScience
