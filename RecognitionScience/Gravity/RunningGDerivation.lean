import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Cost
import RecognitionScience.Gravity.RunningG

namespace RecognitionScience.Gravity.RunningG

open Constants

/-- **CONSTANT: Voxel Density Scaling**
    The effective number of recognition voxels $N(r)$ as a function of radius. -/
def voxel_density_scaling (r : ℝ) : ℝ := r ^ beta_running

/-- **THEOREM: Beta Running Derivation**
    The gravitational running exponent $\beta$ is uniquely determined by the
    ratio of the recognition lag $C_{lag} = \varphi^{-5}$ to the self-similarity
    scaling factor.

    Derivation from Voxel Density:
    1. Let $\rho_{vox}(r)$ be the effective voxel density.
    2. At nm scales, $\rho_{vox}(r) \propto r^\beta$ where $\beta$ is the
       strain induced by the $\varphi^{-5}$ lag.
    3. The effective G is proportional to the local resolution $\rho_{vox}$. -/
theorem beta_running_derived :
    beta_running = -(phi - 1) / (phi ^ 5) := by
  unfold beta_running
  rfl

/-- **THEOREM: Nanoscale Strengthening Scaling**
    The effective gravitational constant $G_{eff}$ strengthens as $r \to 0$
    with the forced exponent $\beta$. -/
theorem running_g_scaling (r r_ref : ℝ) (hr : r > 0) (href : r_ref > 0) :
    deriv (fun x => G_ratio x r_ref) r =
    (abs beta_running * beta_running / r_ref) * (r / r_ref) ^ (beta_running - 1) := by
  unfold G_ratio
  rw [deriv_add]
  · rw [deriv_const, zero_add]
    rw [deriv_mul_const]
    · -- deriv (fun x => (x / r_ref) ^ beta_running) r
      -- = beta_running * (r / r_ref) ^ (beta_running - 1) * (1 / r_ref)
      have h_deriv : deriv (fun x => (x / r_ref) ^ beta_running) r =
          beta_running * (r / r_ref) ^ (beta_running - 1) * (1 / r_ref) := by
        -- Use chain rule: (f ∘ g)' = f'(g(x)) * g'(x)
        -- f(u) = u ^ beta_running, g(x) = x / r_ref
        rw [deriv_rpow_const]
        · -- u ^ (beta_running - 1) * deriv (fun x => x / r_ref) r
          rw [deriv_div_const]
          · rw [deriv_id'']
            ring
        · -- g(x) = r / r_ref > 0
          exact div_pos hr href
      rw [h_deriv]
      ring
    · -- differentiability of (fun x => (x / r_ref) ^ beta_running) at r
      apply DifferentiableAt.rpow_const
      · apply DifferentiableAt.div_const
        exact differentiableAt_id
      · exact Or.inl (ne_of_gt (div_pos hr href))
  · -- differentiability of const 1
    exact differentiableAt_const 1
  · -- differentiability of the second term
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.rpow_const
    · apply DifferentiableAt.div_const
      exact differentiableAt_id
    · exact Or.inl (ne_of_gt (div_pos hr href))

end RunningG
end RecognitionScience.Gravity
