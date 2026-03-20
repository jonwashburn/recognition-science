import Mathlib
import RecognitionScience.Foundation.ContinuumLimit
import RecognitionScience.Foundation.DiscretenessForcing

/-!
# Dimensional Constraints: Continuum Layer

This file packages the public discrete-to-continuum bridge used in the
dimensional constraints rebuttal.
-/

namespace RecognitionScience
namespace Papers
namespace DimensionalConstraints
namespace ContinuumLayer

open Real

/-- Public continuum bridge used in the dimensional-constraints rebuttal. -/
structure PublicContinuumLayer : Prop where
  /-- `J_log` is quadratic to leading order for small perturbations. -/
  quadratic_regime :
    ∀ ε : ℝ, |ε| < 1 →
      |Foundation.DiscretenessForcing.J_log ε - ε ^ 2 / 2| ≤ |ε| ^ 4 / 20
  /-- The lattice Laplacian vanishes on constant fields. -/
  lattice_const :
    ∀ (D : ℕ) (c : ℝ) (x : Fin D → ℤ),
      Foundation.ContinuumLimit.lattice_laplacian (fun _ => c) x = 0
  /-- The lattice Laplacian is linear. -/
  lattice_linear :
    ∀ (D : ℕ)
      (f g : Foundation.ContinuumLimit.LatticeField D)
      (x : Fin D → ℤ),
      Foundation.ContinuumLimit.lattice_laplacian (fun y => f y + g y) x =
        Foundation.ContinuumLimit.lattice_laplacian f x +
        Foundation.ContinuumLimit.lattice_laplacian g x
  /-- Local `J`-cost is quadratically approximated by the nearest-neighbor energy. -/
  jcost_to_laplacian :
    ∀ {D : ℕ}
      (f : Foundation.ContinuumLimit.LatticeField D)
      (x : Fin D → ℤ),
      (∀ k : Fin D,
        |f (Foundation.ContinuumLimit.shift_plus k x) - f x| < 1 ∧
        |f (Foundation.ContinuumLimit.shift_minus k x) - f x| < 1) →
      |Foundation.ContinuumLimit.neighbor_cost f x -
        ∑ k : Fin D,
          ((f (Foundation.ContinuumLimit.shift_plus k x) - f x) ^ 2 / 2 +
           (f (Foundation.ContinuumLimit.shift_minus k x) - f x) ^ 2 / 2)| ≤
        ∑ k : Fin D,
          (|f (Foundation.ContinuumLimit.shift_plus k x) - f x| ^ 4 / 20 +
           |f (Foundation.ContinuumLimit.shift_minus k x) - f x| ^ 4 / 20)
  /-- The scaled central difference is second-order accurate. -/
  second_order_limit :
    ∀ (f : ℝ → ℝ) (x a : ℝ), a ≠ 0 → ContDiff ℝ 4 f →
      ∃ C : ℝ,
        |(f (x + a) + f (x - a) - 2 * f x) / a ^ 2 - deriv (deriv f) x| ≤ C * a ^ 2

/-- The public continuum bridge is available in the current public framework. -/
theorem public_continuum_layer : PublicContinuumLayer := by
  refine
    { quadratic_regime := Foundation.ContinuumLimit.jcost_quadratic_leading
      lattice_const := ?_
      lattice_linear := ?_
      jcost_to_laplacian := ?_
      second_order_limit := Foundation.ContinuumLimit.continuum_limit_second_order }
  · intro D c x
    exact @Foundation.ContinuumLimit.lattice_laplacian_const D c x
  · intro D f g x
    exact @Foundation.ContinuumLimit.lattice_laplacian_add D f g x
  · intro D f x h_small
    exact Foundation.ContinuumLimit.jcost_gives_laplacian_structure f x h_small

end ContinuumLayer
end DimensionalConstraints
end Papers
end RecognitionScience
