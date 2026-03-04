-- import RecognitionScience.Cost.Ndim.Hessian  -- [not in public release]

/-!
# Cost metric in log coordinates
-/

namespace RecognitionScience
namespace Cost
namespace Ndim

/-- Hessian-derived metric entry for `JlogN` in log coordinates. -/
noncomputable def metricEntry {n : ℕ} (α t : Vec n) (i j : Fin n) : ℝ :=
  α i * α j * Real.cosh (dot α t)

@[simp] theorem metricEntry_zero {n : ℕ} (α : Vec n) (i j : Fin n) :
    metricEntry α (fun _ => 0) i j = α i * α j := by
  have hdot : dot α (fun _ => 0) = 0 := by
    unfold dot
    simp
  unfold metricEntry
  rw [hdot, Real.cosh_zero]
  ring

/-- The metric at equilibrium coincides with the outer-product Hessian model. -/
theorem metric_at_equilibrium_eq_hessian {n : ℕ} (α : Vec n) :
    metricEntry α (fun _ => 0) = hessianMatrix α := by
  funext i j
  simp [hessianMatrix, metricEntry_zero]

end Ndim
end Cost
end RecognitionScience
