import Mathlib

namespace RecognitionScience
namespace Cost
namespace FunctionalEquation

open Real
open MeasureTheory
open scoped Topology

/-- Integrating the d'Alembert equation over a symmetric interval gives an
interval-average identity for `H`. -/
theorem dAlembert_average_identity (H : ℝ → ℝ)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u)
    (x h : ℝ) :
    ∫ y in x - h..x + h, H y = 2 * H x * ∫ y in 0..h, H y := by
  have hInt_sub : IntervalIntegrable (fun y : ℝ => H (x - y)) volume 0 h := by
    exact (h_cont.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 h
  have hInt_add : IntervalIntegrable (fun y : ℝ => H (x + y)) volume 0 h := by
    exact (h_cont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 h
  have hshift_add :
      (∫ y in 0..h, H (x + y)) = ∫ y in x..x + h, H y := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_add_right (f := H) (a := 0) (b := h) x)
  have hshift_sub :
      (∫ y in 0..h, H (x - y)) = ∫ y in x - h..x, H y := by
    simpa using
      (intervalIntegral.integral_comp_sub_left (f := H) (a := 0) (b := h) x)
  calc
    ∫ y in x - h..x + h, H y
        = (∫ y in x - h..x, H y) + ∫ y in x..x + h, H y := by
            symm
            exact intervalIntegral.integral_add_adjacent_intervals
              (h_cont.intervalIntegrable (x - h) x)
              (h_cont.intervalIntegrable x (x + h))
    _ = (∫ y in 0..h, H (x - y)) + ∫ y in 0..h, H (x + y) := by
          rw [← hshift_sub, ← hshift_add]
    _ = ∫ y in 0..h, (H (x - y) + H (x + y)) := by
          symm
          exact intervalIntegral.integral_add hInt_sub hInt_add
    _ = ∫ y in 0..h, 2 * H x * H y := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun y _ => by
            rw [add_comm]
            exact h_dAlembert x y
    _ = 2 * H x * ∫ y in 0..h, H y := by
          simpa using
            (intervalIntegral.integral_const_mul (a := 0) (b := h) (r := 2 * H x) (f := H))

/-- Because `H(0) = 1` and `H` is continuous, some short interval average of `H`
is strictly positive. -/
theorem dAlembert_exists_positive_average (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H) :
    ∃ h > 0, 0 < ∫ y in 0..h, H y := by
  have h_mem : H ⁻¹' Set.Ioi ((1 : ℝ) / 2) ∈ 𝓝 (0 : ℝ) := by
    refine h_cont.continuousAt.preimage_mem_nhds ?_
    refine IsOpen.mem_nhds isOpen_Ioi ?_
    simpa [h_one] using (show ((1 : ℝ) / 2) < 1 by norm_num)
  rcases mem_nhds_iff_exists_Ioo_subset.mp h_mem with ⟨a, b, hab, hsub⟩
  let h : ℝ := min (-a) b / 2
  have hmin_pos : 0 < min (-a) b := by
    have ha_pos : 0 < -a := by linarith [hab.1]
    exact lt_min ha_pos hab.2
  have h_pos : 0 < h := by
    dsimp [h]
    linarith
  have h_lt_min : h < min (-a) b := by
    dsimp [h]
    linarith
  have h_lt_b : h < b := lt_of_lt_of_le h_lt_min (min_le_right _ _)
  have h_half : ∀ y ∈ Set.Icc (0 : ℝ) h, (1 : ℝ) / 2 < H y := by
    intro y hy
    have hy_gt_a : a < y := lt_of_lt_of_le hab.1 hy.1
    have hy_lt_b : y < b := lt_of_le_of_lt hy.2 h_lt_b
    exact hsub ⟨hy_gt_a, hy_lt_b⟩
  refine ⟨h, h_pos, ?_⟩
  refine intervalIntegral.integral_pos h_pos h_cont.continuousOn ?_ ?_
  · intro y hy
    linarith [h_half y ⟨hy.1.le, hy.2⟩]
  · refine ⟨0, by simp [h_pos.le], ?_⟩
    simpa [h_one]

/-- Once the short interval average is nonzero, `H` is differentiable and its
derivative is given by a difference quotient with fixed span `h`. -/
theorem dAlembert_hasDerivAt_of_average_nonzero (H : ℝ → ℝ)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u)
    {h : ℝ}
    (h_avg_ne : 2 * ∫ y in 0..h, H y ≠ 0) :
    ∀ x, HasDerivAt H ((H (x + h) - H (x - h)) / (2 * ∫ y in 0..h, H y)) x := by
  let F : ℝ → ℝ := fun u => ∫ t in 0..u, H t
  have hF : ∀ z, HasDerivAt F (H z) z := by
    intro z
    simpa [F] using (h_cont.integral_hasStrictDerivAt 0 z).hasDerivAt
  have h_repr :
      ∀ x, H x = (F (x + h) - F (x - h)) / (2 * ∫ y in 0..h, H y) := by
    intro x
    let c : ℝ := 2 * ∫ y in 0..h, H y
    have hc : c ≠ 0 := h_avg_ne
    have h_interval :
        F (x + h) - F (x - h) = ∫ y in x - h..x + h, H y := by
      simpa [F] using
        (intervalIntegral.integral_interval_sub_left (f := H) (μ := volume)
          (a := 0) (b := x + h) (c := x - h)
          (h_cont.intervalIntegrable 0 (x + h))
          (h_cont.intervalIntegrable 0 (x - h)))
    have h_scaled :
        F (x + h) - F (x - h) = c * H x := by
      calc
        F (x + h) - F (x - h)
            = ∫ y in x - h..x + h, H y := h_interval
        _ = 2 * H x * ∫ y in 0..h, H y := dAlembert_average_identity H h_cont h_dAlembert x h
        _ = c * H x := by
              dsimp [c]
              ring
    calc
      H x = (c * H x) / c := by
              field_simp [c, hc]
      _ = (F (x + h) - F (x - h)) / c := by
              rw [h_scaled]
      _ = (F (x + h) - F (x - h)) / (2 * ∫ y in 0..h, H y) := by
              rfl
  intro x
  have h_shift_add : HasDerivAt (fun u : ℝ => u + h) 1 x := by
    simpa using (hasDerivAt_id x).add_const h
  have h_shift_sub : HasDerivAt (fun u : ℝ => u - h) 1 x := by
    simpa using (hasDerivAt_id x).sub_const h
  have h_num :
      HasDerivAt (fun u => F (u + h) - F (u - h)) (H (x + h) - H (x - h)) x := by
    simpa [Function.comp] using
      (((hF (x + h)).comp x h_shift_add).sub ((hF (x - h)).comp x h_shift_sub))
  have h_div :
      HasDerivAt
        (fun u => (F (u + h) - F (u - h)) / (2 * ∫ y in 0..h, H y))
        ((H (x + h) - H (x - h)) / (2 * ∫ y in 0..h, H y)) x := by
    exact h_num.div_const (2 * ∫ y in 0..h, H y)
  convert h_div using 1
  ext u
  exact h_repr u

/-- Continuous d'Alembert solutions are smooth.

Instead of importing Aczél's classification as an axiom, we bootstrap regularity
from the interval-average identity:

`∫_{x-h}^{x+h} H = 2 H(x) ∫_0^h H`.

For some small `h`, the denominator is nonzero because `H(0)=1` and `H` is
continuous. This expresses `H` as a moving interval average of itself, hence as
a differentiable function. Repeating the same argument on the derivative yields
`C^∞` regularity. -/
theorem aczel_representation_axiom (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) H := by
  obtain ⟨h, h_pos, h_avg_pos⟩ := dAlembert_exists_positive_average H h_one h_cont
  have h_avg_ne : 2 * ∫ y in 0..h, H y ≠ 0 := by
    have : 0 < 2 * ∫ y in 0..h, H y := by nlinarith
    exact this.ne'
  have h_hasDerivAt :
      ∀ x, HasDerivAt H ((H (x + h) - H (x - h)) / (2 * ∫ y in 0..h, H y)) x :=
    dAlembert_hasDerivAt_of_average_nonzero H h_cont h_dAlembert h_avg_ne
  have hDiff : Differentiable ℝ H := fun x => (h_hasDerivAt x).differentiableAt
  have h_deriv_formula :
      deriv H = fun x => (H (x + h) - H (x - h)) / (2 * ∫ y in 0..h, H y) := by
    funext x
    exact (h_hasDerivAt x).deriv
  have h_nat : ∀ n : ℕ, ContDiff ℝ n H := by
    intro n
    induction n with
    | zero =>
        simpa [contDiff_zero] using h_cont
    | succ n ih =>
        have hDerivCont : ContDiff ℝ n (deriv H) := by
          rw [h_deriv_formula]
          have h_add_map : ContDiff ℝ n (fun x : ℝ => x + h) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (contDiff_id.add contDiff_const : ContDiff ℝ n (fun x : ℝ => x + h))
          have h_sub_map : ContDiff ℝ n (fun x : ℝ => x - h) := by
            simpa using (contDiff_id.sub contDiff_const : ContDiff ℝ n (fun x : ℝ => x - h))
          have h_add : ContDiff ℝ n (fun x : ℝ => H (x + h)) := ih.comp h_add_map
          have h_sub : ContDiff ℝ n (fun x : ℝ => H (x - h)) := ih.comp h_sub_map
          exact (h_add.sub h_sub).div_const (2 * ∫ y in 0..h, H y)
        simpa using (contDiff_succ_iff_deriv.2 ⟨hDiff, by simp, hDerivCont⟩)
  simpa using (contDiff_infty.2 h_nat)

/-- Smoothness of continuous d'Alembert solutions.
Direct consequence of the Aczél classification theorem. -/
theorem aczel_dAlembert_smooth (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) H :=
  aczel_representation_axiom H h_one h_cont h_dAlembert

end FunctionalEquation
end Cost
end RecognitionScience
