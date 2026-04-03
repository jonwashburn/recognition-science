import Mathlib
import RecognitionScience.Measurement.PathAction
import RecognitionScience.Measurement.TwoBranchGeodesic
import RecognitionScience.Measurement.KernelMatch

/-!
# The C = 2A Measurement Bridge

This module proves the central equivalence between recognition cost C
and the residual-model rate action A.

Main theorem: For any two-branch geodesic rotation,
  C = 2A  (exactly)

This establishes that quantum measurement and recognition are governed
by the same unique cost functional J.
-/

namespace RecognitionScience
namespace Measurement

open Real Cost

/-! ## Improper Integral Axioms -/


/-- Construct recognition path from geodesic rotation using recognition profile -/
noncomputable def pathFromRotation (rot : TwoBranchRotation) : RecognitionPath where
  T := π/2 - rot.θ_s
  T_pos := by
    have ⟨_, h2⟩ := rot.θ_s_bounds
    linarith
  rate := fun ϑ => recognitionProfile (ϑ + rot.θ_s)
  rate_pos := by
    intro t ht
    apply recognitionProfile_pos
    have ⟨h1, h2⟩ := rot.θ_s_bounds
    constructor
    · -- 0 ≤ t + θ_s
      have := ht.1
      linarith
    · -- t + θ_s ≤ π/2
      have ht' : t ≤ π/2 - rot.θ_s := ht.2
      have := add_le_add_right ht' rot.θ_s
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

/-- The integral of tan from θ_s to π/2 equals -ln(sin θ_s) -/
theorem integral_cot_from_theta (θ_s : ℝ) (hθ : 0 < θ_s ∧ θ_s < π/2) :
  ∫ θ in θ_s..(π/2), Real.cot θ = - Real.log (Real.sin θ_s) := by
  -- Standard calculus result: ∫ cot θ dθ = log(sin θ) + C.
  -- We prove it via FTC on `f(θ) = log(sin θ)` over `[θ_s, π/2]`.
  let f : ℝ → ℝ := fun θ => Real.log (Real.sin θ)

  have hpi2ltpi : (Real.pi / 2 : ℝ) < Real.pi := by nlinarith [Real.pi_pos]

  have hsin_ne0_uIcc : ∀ x ∈ Set.uIcc θ_s (π/2), Real.sin x ≠ 0 := by
    intro x hx
    have hx' : θ_s ≤ x ∧ x ≤ π/2 := by
      rcases Set.mem_uIcc.mp hx with hx' | hx'
      · exact hx'
      · exfalso
        have : (π/2 : ℝ) ≤ θ_s := le_trans hx'.1 hx'.2
        exact (not_le_of_lt hθ.2) this
    have hxpos : 0 < x := lt_of_lt_of_le hθ.1 hx'.1
    have hxltpi : x < Real.pi := lt_of_le_of_lt hx'.2 hpi2ltpi
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos hxltpi)

  have hderiv_eq_cot_uIoc : Set.EqOn (fun x => deriv f x) (fun x => Real.cot x) (Set.uIoc θ_s (π/2)) := by
    intro x hx
    have hx' : θ_s < x ∧ x ≤ π/2 := by
      rcases Set.mem_uIoc.mp hx with hx' | hx'
      · exact hx'
      · exfalso
        have : (π/2 : ℝ) ≤ θ_s := le_trans (le_of_lt hx'.1) hx'.2
        exact (not_le_of_lt hθ.2) this
    have hxpos : 0 < x := lt_of_lt_of_le hθ.1 (le_of_lt hx'.1)
    have hxltpi : x < Real.pi := lt_of_le_of_lt hx'.2 hpi2ltpi
    have hsx : Real.sin x ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos hxltpi)
    have hlog : HasDerivAt Real.log (Real.sin x)⁻¹ (Real.sin x) := Real.hasDerivAt_log hsx
    have hsin : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
    have hcomp :
        HasDerivAt (fun t => Real.log (Real.sin t)) ((Real.sin x)⁻¹ * Real.cos x) x :=
      (HasDerivAt.comp x hlog hsin)
    -- Turn the computed derivative into `deriv f x = cot x`.
    have hderiv : deriv (fun t => Real.log (Real.sin t)) x = (Real.sin x)⁻¹ * Real.cos x := hcomp.deriv
    have hmul_to_div : (Real.sin x)⁻¹ * Real.cos x = Real.cos x / Real.sin x := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    calc
      deriv f x = (Real.sin x)⁻¹ * Real.cos x := by simpa [f] using hderiv
      _ = Real.cos x / Real.sin x := hmul_to_div
      _ = Real.cot x := by simpa using (Real.cot_eq_cos_div_sin x).symm

  have hdiff : ∀ x ∈ Set.uIcc θ_s (π/2), DifferentiableAt ℝ f x := by
    intro x hx
    have hsx : Real.sin x ≠ 0 := hsin_ne0_uIcc x hx
    have hlog : HasDerivAt Real.log (Real.sin x)⁻¹ (Real.sin x) := Real.hasDerivAt_log hsx
    have hsin : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
    have hcomp : HasDerivAt (fun t => Real.log (Real.sin t)) ((Real.sin x)⁻¹ * Real.cos x) x :=
      (HasDerivAt.comp x hlog hsin)
    -- `f` is definitionally the same function.
    simpa [f] using hcomp.differentiableAt

  have hCotCont : ContinuousOn (fun x => Real.cot x) (Set.uIcc θ_s (π/2)) := by
    -- On `[θ_s, π/2]` we have `sin x ≠ 0`, so `cot x = cos x / sin x` is continuous.
    have hcos : ContinuousOn Real.cos (Set.uIcc θ_s (π/2)) :=
      (Real.continuous_cos.continuousOn)
    have hsin : ContinuousOn Real.sin (Set.uIcc θ_s (π/2)) :=
      (Real.continuous_sin.continuousOn)
    have hsin_ne0 : ∀ x ∈ Set.uIcc θ_s (π/2), Real.sin x ≠ 0 := hsin_ne0_uIcc
    have hdiv : ContinuousOn (fun x => Real.cos x / Real.sin x) (Set.uIcc θ_s (π/2)) :=
      (hcos.div hsin hsin_ne0)
    simpa [Real.cot_eq_cos_div_sin] using hdiv

  have hCotInt : IntervalIntegrable (fun x => Real.cot x) MeasureTheory.volume θ_s (π/2) :=
    hCotCont.intervalIntegrable

  have hDerivInt : IntervalIntegrable (fun x => deriv f x) MeasureTheory.volume θ_s (π/2) := by
    have hEq : Set.EqOn (fun x => Real.cot x) (fun x => deriv f x) (Set.uIoc θ_s (π/2)) := by
      intro x hx
      simpa using (hderiv_eq_cot_uIoc hx).symm
    exact (IntervalIntegrable.congr hEq) hCotInt

  have hFTC :
      ∫ x in θ_s..(π/2), deriv f x = f (π/2) - f θ_s :=
    intervalIntegral.integral_deriv_eq_sub (a := θ_s) (b := (π/2)) hdiff hDerivInt

  have hcongr :
      (∫ x in θ_s..(π/2), Real.cot x) = (∫ x in θ_s..(π/2), deriv f x) := by
    have h_ae :
        ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc θ_s (π/2) → Real.cot x = deriv f x := by
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact (hderiv_eq_cot_uIoc hx).symm
    simpa using
      (intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume) (a := θ_s) (b := (π/2))
        (f := fun x => Real.cot x) (g := fun x => deriv f x) h_ae)

  -- Finish: evaluate endpoints.
  have hsθ : Real.sin θ_s ≠ 0 := by
    have hθltpi : θ_s < Real.pi := lt_of_lt_of_le hθ.2 (le_of_lt hpi2ltpi)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθltpi)

  calc
    ∫ x in θ_s..(π/2), Real.cot x
        = ∫ x in θ_s..(π/2), deriv f x := hcongr
    _ = f (π/2) - f θ_s := hFTC
    _ = Real.log (Real.sin (π/2)) - Real.log (Real.sin θ_s) := by rfl
    _ = - Real.log (Real.sin θ_s) := by simp [Real.sin_pi_div_two]

/-- Main C=2A Bridge Theorem:
    The recognition action for the constructed path equals twice the rate action -/
theorem measurement_bridge_C_eq_2A (rot : TwoBranchRotation) :
  pathAction (pathFromRotation rot) = 2 * rateAction rot := by
  unfold pathAction pathFromRotation rateAction
  simp
  have hkernel : ∫ ϑ in (0)..(π/2 - rot.θ_s),
                   Jcost (recognitionProfile (ϑ + rot.θ_s)) =
                2 * ∫ ϑ in (0)..(π/2 - rot.θ_s), Real.cot (ϑ + rot.θ_s) :=
    kernel_integral_match rot.θ_s rot.θ_s_bounds
  rw [hkernel]
  have h_subst :
      ∫ ϑ in (0)..(π/2 - rot.θ_s), Real.cot (ϑ + rot.θ_s)
        = ∫ θ in rot.θ_s..(π/2), Real.cot θ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using
        (intervalIntegral.integral_comp_add_right
          (a := (0 : ℝ)) (b := π/2 - rot.θ_s)
          (f := fun θ => Real.cot θ) (d := rot.θ_s))
  have hI := integral_cot_from_theta rot.θ_s rot.θ_s_bounds
  have htan :
      ∫ ϑ in (0)..(π/2 - rot.θ_s), Real.cot (ϑ + rot.θ_s)
        = - Real.log (Real.sin rot.θ_s) := by
    simpa [h_subst] using hI
  simp [htan, two_mul, mul_left_comm, mul_assoc]

/-- Weight bridge: w = exp(-C) = exp(-2A) -/
theorem weight_bridge (rot : TwoBranchRotation) :
  pathWeight (pathFromRotation rot) = Real.exp (- 2 * rateAction rot) := by
  unfold pathWeight
  rw [measurement_bridge_C_eq_2A]
  congr 1
  ring

/-- Weight equals Born probability: exp(-2A) = |α₂|² -/
theorem weight_equals_born (rot : TwoBranchRotation) :
  pathWeight (pathFromRotation rot) = initialAmplitudeSquared rot := by
  unfold pathWeight initialAmplitudeSquared
  rw [measurement_bridge_C_eq_2A]
  have h := Measurement.born_weight_from_rate rot
  have hWeight :
      Real.exp (-(2 * rateAction rot)) = initialAmplitudeSquared rot := by
    simpa [rateAction, Measurement.initialAmplitudeSquared] using h
  simpa using hWeight

/-- Amplitude bridge modulus: |𝒜| = exp(-A) -/
theorem amplitude_modulus_bridge (rot : TwoBranchRotation) (φ : ℝ) :
  ‖pathAmplitude (pathFromRotation rot) φ‖ = Real.exp (- rateAction rot) := by
  unfold pathAmplitude
  have hExpReal :
      ‖Complex.exp (-(pathAction (pathFromRotation rot)) / 2)‖ =
        Real.exp (-(pathAction (pathFromRotation rot)) / 2) := by
    simpa using Complex.norm_exp_ofReal (-(pathAction (pathFromRotation rot)) / 2)
  have hExpI :
      ‖Complex.exp (φ * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I φ
  have hAction :
      -(pathAction (pathFromRotation rot)) / 2 = - rateAction rot := by
    have h := measurement_bridge_C_eq_2A rot
    calc
      -(pathAction (pathFromRotation rot)) / 2
          = -(2 * rateAction rot) / 2 := by simpa [h]
      _ = - rateAction rot := by ring
  calc
    ‖Complex.exp (-(pathAction (pathFromRotation rot)) / 2)
        * Complex.exp (φ * Complex.I)‖
        = ‖Complex.exp (-(pathAction (pathFromRotation rot)) / 2)‖ *
          ‖Complex.exp (φ * Complex.I)‖ := by simpa using norm_mul _ _
    _ = Real.exp (-(pathAction (pathFromRotation rot)) / 2) * 1 := by
        simpa [hExpReal, hExpI]
    _ = Real.exp (- rateAction rot) := by
        simpa [hAction]

end Measurement
end RecognitionScience
