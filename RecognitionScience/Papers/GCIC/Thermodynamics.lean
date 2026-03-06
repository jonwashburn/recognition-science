import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Cost
import RecognitionScience.Foundation.DiscretenessForcing
import RecognitionScience.Numerics.Interval.Log

/-!
# GCIC Phase Thermodynamics: Stiffness, Barrier, and Phase Structure

Formalizes the key constants from the GCIC Response paper
"Two Upgrades for the GCIC Paper" (Feb 2026).
-/

namespace RecognitionScience
namespace Papers.GCIC
namespace Thermodynamics

open Real

/-- log(Constants.phi) > 0.48. Inherited from the Numerics log-bound on goldenRatio. -/
private lemma log_phi_gt_048 : (0.48 : ℝ) < Real.log Constants.phi := by
  have h := RecognitionScience.Numerics.log_phi_gt_048
  simpa [RecognitionScience.Constants.phi, Real.goldenRatio] using h

/-- log(Constants.phi) < 0.483. -/
private lemma log_phi_lt_0483 : Real.log Constants.phi < (0.483 : ℝ) := by
  have h := RecognitionScience.Numerics.log_phi_lt_0483
  simpa [RecognitionScience.Constants.phi, Real.goldenRatio] using h

/-! ## Part I: GCIC Constants -/

/-- **GCIC STIFFNESS CONSTANT**: κ = (ln φ)²/2 ≈ 0.116. -/
noncomputable def gcic_stiffness : ℝ := (Real.log Constants.phi) ^ 2 / 2

theorem gcic_stiffness_pos : 0 < gcic_stiffness := by
  unfold gcic_stiffness
  apply div_pos _ (by norm_num)
  exact pow_pos (Real.log_pos Constants.one_lt_phi) 2

/-- κ ∈ (0.1152, 0.1167). -/
theorem gcic_stiffness_bounds :
    (0.1152 : ℝ) < gcic_stiffness ∧ gcic_stiffness < 0.1167 := by
  unfold gcic_stiffness
  have hlo := log_phi_gt_048
  have hhi := log_phi_lt_0483
  constructor <;> nlinarith [sq_nonneg (Real.log Constants.phi - 0.48),
                              sq_nonneg (Real.log Constants.phi - 0.483),
                              sq_nonneg (Real.log Constants.phi)]

/-- **PHASE BARRIER**: J̃(1/2) = cosh(ln φ/2) - 1 ≈ 0.029. -/
noncomputable def phase_barrier : ℝ :=
  Real.cosh (Real.log Constants.phi / 2) - 1

theorem phase_barrier_pos : 0 < phase_barrier := by
  unfold phase_barrier
  have hne : Real.log Constants.phi / 2 ≠ 0 := by
    apply div_ne_zero _ two_ne_zero
    exact Real.log_ne_zero_of_pos_of_ne_one Constants.phi_pos (ne_of_gt Constants.one_lt_phi)
  have hgt : 1 < Real.cosh (Real.log Constants.phi / 2) := Real.one_lt_cosh.mpr hne
  linarith

/-- J̃(1/2) lower bound: phase_barrier ≥ 0.0287.
    Proof: log φ / 2 > 0.24, cosh(0.24) ≥ 1 + 0.24²/2 = 1.0288. -/
theorem phase_barrier_lower : (0.0287 : ℝ) ≤ phase_barrier := by
  unfold phase_barrier
  have hlo := log_phi_gt_048
  have hmono_lo : Real.cosh 0.24 ≤ Real.cosh (Real.log Constants.phi / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.24),
        abs_of_nonneg (by linarith)]; linarith
  have h_lo_val : 1.0288 ≤ Real.cosh 0.24 := by
    have h := Cost.cosh_quadratic_lower_bound 0.24; norm_num at h; linarith
  linarith

/-- J̃(1/2) upper bound: phase_barrier < 0.032.
    Numerically: cosh(log φ/2) ≈ cosh(0.241) ≈ 1.0293 < 1.032.
    Proof: cosh_quadratic_bound gives |cosh x - 1 - x²/2| ≤ x⁴/20 for |x| < 1.
    With x = log φ/2 < 0.2415, we get cosh x ≤ 1 + x²/2 + x⁴/20 < 1.032. -/
theorem phase_barrier_upper : phase_barrier < 0.032 := by
  unfold phase_barrier
  have hx_pos : 0 < Real.log Constants.phi / 2 := div_pos (Real.log_pos Constants.one_lt_phi) (by norm_num)
  have hx_lt : Real.log Constants.phi / 2 < (0.242 : ℝ) := by linarith [log_phi_lt_0483]
  have hx_abs : |Real.log Constants.phi / 2| < 1 := by rw [abs_of_pos hx_pos]; linarith
  have hbound := Foundation.DiscretenessForcing.cosh_quadratic_bound (Real.log Constants.phi / 2) hx_abs
  have hx_sq : (Real.log Constants.phi / 2) ^ 2 < (0.0586 : ℝ) := by
    calc (Real.log Constants.phi / 2) ^ 2 < (0.242 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hx_lt
      _ = 0.058564 := by norm_num
      _ < 0.0586 := by norm_num
  have hx_four : (Real.log Constants.phi / 2) ^ 4 < (0.00344 : ℝ) := by
    have hsq : (Real.log Constants.phi / 2) ^ 2 < (0.242 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hx_lt
    have hneg : -((0.242 : ℝ) ^ 2) < (Real.log Constants.phi / 2) ^ 2 := by
      have : 0 ≤ (Real.log Constants.phi / 2) ^ 2 := sq_nonneg _
      linarith
    calc (Real.log Constants.phi / 2) ^ 4 = ((Real.log Constants.phi / 2) ^ 2) ^ 2 := by ring
      _ < ((0.242 : ℝ) ^ 2) ^ 2 := sq_lt_sq' hneg hsq
      _ = (0.242 : ℝ) ^ 4 := by ring
      _ < 0.00344 := by norm_num
  have h_rest : Real.cosh (Real.log Constants.phi / 2) - 1 - (Real.log Constants.phi / 2) ^ 2 / 2 ≤
      (Real.log Constants.phi / 2) ^ 4 / 20 := by
    rw [abs_le] at hbound; exact hbound.2
  calc Real.cosh (Real.log Constants.phi / 2) - 1
      = (Real.cosh (Real.log Constants.phi / 2) - 1 - (Real.log Constants.phi / 2) ^ 2 / 2) +
          (Real.log Constants.phi / 2) ^ 2 / 2 := by ring
    _ ≤ (Real.log Constants.phi / 2) ^ 4 / 20 + (Real.log Constants.phi / 2) ^ 2 / 2 := by linarith
    _ < 0.00344 / 20 + 0.0586 / 2 := by nlinarith
    _ = 0.029472 := by norm_num
    _ < 0.032 := by norm_num

/-- **MEAN-FIELD CRITICAL TEMPERATURE**: TRc,MF = 3(ln φ)² ≈ 0.694 (d=3, z=6). -/
noncomputable def mf_critical_temperature : ℝ := 3 * (Real.log Constants.phi) ^ 2

theorem mf_critical_temperature_pos : 0 < mf_critical_temperature := by
  unfold mf_critical_temperature
  apply mul_pos (by norm_num)
  exact pow_pos (Real.log_pos Constants.one_lt_phi) 2

/-- TRc,MF ∈ (0.691, 0.701). -/
theorem mf_critical_temperature_bounds :
    (0.691 : ℝ) < mf_critical_temperature ∧ mf_critical_temperature < 0.701 := by
  unfold mf_critical_temperature
  have hlo := log_phi_gt_048
  have hhi := log_phi_lt_0483
  constructor <;> nlinarith [sq_nonneg (Real.log Constants.phi - 0.48),
                              sq_nonneg (Real.log Constants.phi - 0.483),
                              sq_nonneg (Real.log Constants.phi)]

theorem mf_temp_eq_six_kappa : mf_critical_temperature = 6 * gcic_stiffness := by
  unfold mf_critical_temperature gcic_stiffness; ring

/-! ## Part II: Uniform Convexity (Proposition 1) -/

/-- V''(t) = cosh(t) ≥ 1 — uniform convexity of the phase potential. -/
theorem noncompact_uniform_convexity (t : ℝ) : 1 ≤ Real.cosh t :=
  Real.one_le_cosh t

/-- cosh(t) - 1 ≥ t²/2 (quadratic lower bound from uniform convexity). -/
theorem jlog_above_half_square (t : ℝ) : t ^ 2 / 2 ≤ Real.cosh t - 1 := by
  have := Cost.cosh_quadratic_lower_bound t; linarith

/-! ## Summary certificate -/

theorem gcic_thermodynamics_cert :
    0 < gcic_stiffness ∧ 0 < phase_barrier ∧ 0 < mf_critical_temperature ∧
    (∀ t, 1 ≤ Real.cosh t) :=
  ⟨gcic_stiffness_pos, phase_barrier_pos, mf_critical_temperature_pos,
   noncompact_uniform_convexity⟩

end Thermodynamics
end Papers.GCIC
end RecognitionScience
