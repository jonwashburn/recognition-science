import Mathlib
import RecognitionScience.Foundation.DimensionForcing

/-!
# Dimensional Constraints: Dimension Layer

This file packages the public dimension-forcing results used in the
dimensional constraints rebuttal.
-/

namespace RecognitionScience
namespace Foundation
namespace DimensionalConstraints
namespace DimensionLayer

/-- Public dimension layer used in the dimensional-constraints rebuttal. -/
structure PublicDimensionLayer : Prop where
  /-- The synchronization period equals `360`. -/
  sync_period :
    Foundation.DimensionForcing.sync_period = 360
  /-- The equation `2^D = 8` forces `D = 3`. -/
  power_of_two_forces_three :
    ∀ D : Foundation.DimensionForcing.Dimension, 2 ^ D = 8 → D = 3
  /-- The eight-tick rule forces `D = 3`. -/
  eight_tick_forces_three :
    ∀ D : Foundation.DimensionForcing.Dimension,
      Foundation.DimensionForcing.EightTickFromDimension D =
        Foundation.DimensionForcing.eight_tick → D = 3
  /-- There is a unique RS-compatible dimension. -/
  unique_dimension :
    ∃! D : Foundation.DimensionForcing.Dimension,
      Foundation.DimensionForcing.RSCompatibleDimension D
  /-- Every RS-compatible dimension equals `3`. -/
  compatible_implies_three :
    ∀ D : Foundation.DimensionForcing.Dimension,
      Foundation.DimensionForcing.RSCompatibleDimension D → D = 3

/-- The public dimension layer is available in the current public framework. -/
theorem public_dimension_layer : PublicDimensionLayer := by
  refine
    { sync_period := Foundation.DimensionForcing.sync_period_eq_360
      power_of_two_forces_three := Foundation.DimensionForcing.power_of_2_forces_D3
      eight_tick_forces_three := Foundation.DimensionForcing.eight_tick_forces_D3
      unique_dimension := Foundation.DimensionForcing.dimension_forced
      compatible_implies_three := ?_ }
  intro D hD
  exact Foundation.DimensionForcing.dimension_unique D hD

end DimensionLayer
end DimensionalConstraints
end Foundation
end RecognitionScience
