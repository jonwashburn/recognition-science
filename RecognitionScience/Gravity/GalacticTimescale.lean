import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Foundation.PhiForcing
-- import RecognitionScience.Numerics.Interval.PhiBounds  -- [not in public release]
-- import RecognitionScience.Numerics.Interval.GalacticBounds  -- [not in public release]

namespace RecognitionScience
namespace Gravity
namespace GalacticTimescale

open Real
open Constants
open Numerics

noncomputable section

/-- The characteristic galactic memory timescale τ★ in seconds. -/
def tau_star_s : ℝ := 133e6 * 365.25 * 24 * 3600

/-- The fundamental RS tick in seconds (SI calibration). -/
def tau0_SI : ℝ := 7.3e-15

/-- The φ-ladder rung function: τ_N = τ₀ · φ^N -/
def phi_rung_time (N : ℝ) : ℝ := tau0_SI * phi ^ N

/-- The log-base-φ of the timescale ratio: N = log_φ(τ★/τ₀) -/
def N_galactic : ℝ := Real.log (tau_star_s / tau0_SI) / Real.log phi

/-- **THEOREM: N_galactic Approximation** -/
theorem N_galactic_approx : 140 < N_galactic ∧ N_galactic < 145 := by
  have h_ratio_val : tau_star_s / tau0_SI = (galactic_ratio_rational : ℝ) := by
    unfold tau_star_s tau0_SI galactic_ratio_rational
    norm_num
  have hlog_phi : 0 < Real.log phi := Real.log_pos Constants.one_lt_phi

  constructor
  · unfold N_galactic
    rw [h_ratio_val]
    apply (lt_div_iff₀ hlog_phi).mpr
    rw [← Real.log_rpow Constants.phi_pos]
    apply Real.log_lt_log (Real.rpow_pos_of_pos Constants.phi_pos 140)
    exact phi_pow_140_lt_ratio
  · unfold N_galactic
    rw [h_ratio_val]
    apply (div_lt_iff₀ hlog_phi).mpr
    rw [← Real.log_rpow Constants.phi_pos]
    apply Real.log_lt_log
    · have h_pos : (0 : ℝ) < (galactic_ratio_rational : ℝ) := by norm_num [galactic_ratio_rational]
      exact h_pos
    · exact ratio_lt_phi_pow_145

/-- **THEOREM: τ★ Lies on the φ-Ladder** -/
theorem tau_star_is_phi_rung :
   ∃ N : ℤ, |tau_star_s - phi_rung_time N| < 0.1 * tau_star_s := by
  use 142
  unfold phi_rung_time
  let ratio := tau_star_s / tau0_SI
  have h_ratio_val : tau_star_s / tau0_SI = (galactic_ratio_rational : ℝ) := by
    unfold tau_star_s tau0_SI galactic_ratio_rational
    norm_num

  have h_in_142 := phi_pow_142_in_interval

  rw [abs_lt]
  constructor
  · -- tau_star - tau0 * phi^142 > -0.1 * tau_star <=> 0.9 * tau_star < tau0 * phi^142
    have h_lo : (0.9 * galactic_ratio_rational : ℝ) < goldenRatio ^ (142 : ℝ) := by
      calc (0.9 * galactic_ratio_rational : ℝ) < (phi_pow_142_interval.lo : ℝ) := by
             exact_mod_cast ratio_0_9_lt_phi_pow_142
        _ ≤ goldenRatio ^ (142 : ℝ) := h_in_142.1
    have h_scale : 0.9 * tau_star_s < tau0_SI * goldenRatio ^ (142 : ℝ) := by
      unfold tau_star_s tau0_SI at h_ratio_val ⊢
      rw [← lt_div_iff₀ (by norm_num : (0 : ℝ) < 7.3e-15)] at h_lo
      -- ratio = tau_star / tau0
      have h_r : tau_star_s / tau0_SI = (galactic_ratio_rational : ℝ) := by
        unfold tau_star_s tau0_SI galactic_ratio_rational; norm_num
      rw [← h_r] at h_lo
      linarith
    linarith
  · -- tau_star - tau0 * phi^142 < 0.1 * tau_star <=> tau0 * phi^142 > 0.9 * tau_star (already checked)
    -- wait, tau_star - tau0 * phi^142 < 0.1 * tau_star <=> 1.1 * tau_star > tau0 * phi^142
    have h_hi : goldenRatio ^ (142 : ℝ) < (1.1 * galactic_ratio_rational : ℝ) := by
      calc goldenRatio ^ (142 : ℝ) ≤ (phi_pow_142_interval.hi : ℝ) := h_in_142.2
        _ < (1.1 * galactic_ratio_rational : ℝ) := by
             exact_mod_cast phi_pow_142_lt_ratio_1_1
    have h_scale : tau0_SI * goldenRatio ^ (142 : ℝ) < 1.1 * tau_star_s := by
      unfold tau_star_s tau0_SI at h_ratio_val ⊢
      rw [← lt_div_iff₀ (by norm_num : (0 : ℝ) < 7.3e-15)] at h_hi
      have h_r : tau_star_s / tau0_SI = (galactic_ratio_rational : ℝ) := by
        unfold tau_star_s tau0_SI galactic_ratio_rational; norm_num
      rw [← h_r] at h_hi
      linarith
    linarith

def galactic_status : List (String × String) :=
  [ ("N_galactic approx", "PROVEN")
  , ("tau_star is phi rung", "PROVEN")
  ]

#eval galactic_status

end
end GalacticTimescale
end Gravity
end RecognitionScience
