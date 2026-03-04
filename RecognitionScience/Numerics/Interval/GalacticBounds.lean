import RecognitionScience.Numerics.Interval.Basic
import RecognitionScience.Numerics.Interval.Pow
import RecognitionScience.Constants

namespace RecognitionScience.Numerics

open Interval
open Real

/-- Ratio τ★ / τ₀ ≈ 5.75e29 -/
def galactic_ratio_rational : ℚ := 41971608 * 10^24 / 73

/-- φ^51 lo > 0 -/
lemma phi_pow_51_lo_pos : (0 : ℚ) < phi_pow_51_interval.lo := by
  unfold phi_pow_51_interval; norm_num

/-- Interval for φ^102 = (φ^51)^2 -/
def phi_pow_102_interval : Interval :=
  mulPos phi_pow_51_interval phi_pow_51_interval phi_pow_51_lo_pos phi_pow_51_lo_pos

/-- φ^16 lo > 0 -/
lemma phi_pow_16_lo_pos : (0 : ℚ) < phi_pow_16_interval.lo := by
  unfold phi_pow_16_interval; norm_num

/-- φ^5 lo > 0 -/
lemma phi_pow_5_lo_pos : (0 : ℚ) < phi_pow_5_interval.lo := by
  unfold phi_pow_5_interval; norm_num

/-- φ lo > 0 -/
lemma phi_lo_pos : (0 : ℚ) < phiInterval.lo := by
  unfold phiInterval; norm_num

/-- Interval for φ^32 = (φ^16)^2 -/
def phi_pow_32_interval : Interval :=
  mulPos phi_pow_16_interval phi_pow_16_interval phi_pow_16_lo_pos phi_pow_16_lo_pos

lemma phi_pow_32_lo_pos : (0 : ℚ) < phi_pow_32_interval.lo := by
  unfold phi_pow_32_interval mulPos; dsimp
  exact mul_pos phi_pow_16_lo_pos phi_pow_16_lo_pos

/-- Interval for φ^37 = φ^32 * φ^5 -/
def phi_pow_37_interval : Interval :=
  mulPos phi_pow_32_interval phi_pow_5_interval phi_pow_32_lo_pos phi_pow_5_lo_pos

lemma phi_pow_37_lo_pos : (0 : ℚ) < phi_pow_37_interval.lo := by
  unfold phi_pow_37_interval mulPos; dsimp
  exact mul_pos phi_pow_32_lo_pos phi_pow_5_lo_pos

/-- Interval for φ^38 = φ^37 * φ^1 -/
def phi_pow_38_interval : Interval :=
  mulPos phi_pow_37_interval phiInterval phi_pow_37_lo_pos phi_lo_pos

lemma phi_pow_102_lo_pos : (0 : ℚ) < phi_pow_102_interval.lo := by
  unfold phi_pow_102_interval mulPos; dsimp
  exact mul_pos phi_pow_51_lo_pos phi_pow_51_lo_pos

lemma phi_pow_38_lo_pos : (0 : ℚ) < phi_pow_38_interval.lo := by
  unfold phi_pow_38_interval mulPos; dsimp
  exact mul_pos phi_pow_37_lo_pos phi_lo_pos

/-- Interval for φ^140 = φ^102 * φ^38 -/
def phi_pow_140_interval : Interval :=
  mulPos phi_pow_102_interval phi_pow_38_interval phi_pow_102_lo_pos phi_pow_38_lo_pos

lemma phi_pow_140_lo_pos : (0 : ℚ) < phi_pow_140_interval.lo := by
  unfold phi_pow_140_interval mulPos; dsimp
  exact mul_pos phi_pow_102_lo_pos phi_pow_38_lo_pos

/-- Interval for φ^145 = φ^140 * φ^5 -/
def phi_pow_145_interval : Interval :=
  mulPos phi_pow_140_interval phi_pow_5_interval phi_pow_140_lo_pos phi_pow_5_lo_pos

theorem phi_pow_140_in_interval : phi_pow_140_interval.contains (goldenRatio ^ (140 : ℝ)) := by
  have h_in_51 : phi_pow_51_interval.contains (goldenRatio ^ (51 : ℝ)) := phi_pow_51_in_interval
  have h_in_102 : phi_pow_102_interval.contains (goldenRatio ^ (102 : ℝ)) := by
    unfold phi_pow_102_interval
    have : goldenRatio ^ (102 : ℝ) = goldenRatio ^ (51 : ℝ) * goldenRatio ^ (51 : ℝ) := by
      rw [← Real.rpow_add goldenRatio_pos]; norm_num
    rw [this]
    apply mulPos_contains_mul phi_pow_51_lo_pos phi_pow_51_lo_pos h_in_51 h_in_51

  have h_in_16 : phi_pow_16_interval.contains (goldenRatio ^ (16 : ℝ)) := phi_pow_16_in_interval
  have h_in_32 : phi_pow_32_interval.contains (goldenRatio ^ (32 : ℝ)) := by
    unfold phi_pow_32_interval
    have : goldenRatio ^ (32 : ℝ) = goldenRatio ^ (16 : ℝ) * goldenRatio ^ (16 : ℝ) := by
      rw [← Real.rpow_add goldenRatio_pos]; norm_num
    rw [this]
    apply mulPos_contains_mul phi_pow_16_lo_pos phi_pow_16_lo_pos h_in_16 h_in_16

  have h_in_5 : phi_pow_5_interval.contains (goldenRatio ^ (5 : ℝ)) := phi_pow_5_in_interval
  have h_in_37 : phi_pow_37_interval.contains (goldenRatio ^ (37 : ℝ)) := by
    unfold phi_pow_37_interval
    have : goldenRatio ^ (37 : ℝ) = goldenRatio ^ (32 : ℝ) * goldenRatio ^ (5 : ℝ) := by
      rw [← Real.rpow_add goldenRatio_pos]; norm_num
    rw [this]
    apply mulPos_contains_mul phi_pow_32_lo_pos phi_pow_5_lo_pos h_in_32 h_in_5

  have h_in_1 : phiInterval.contains goldenRatio := phi_in_phiInterval
  have h_in_38 : phi_pow_38_interval.contains (goldenRatio ^ (38 : ℝ)) := by
    unfold phi_pow_38_interval
    have : goldenRatio ^ (38 : ℝ) = goldenRatio ^ (37 : ℝ) * goldenRatio ^ (1 : ℝ) := by
      rw [← Real.rpow_add goldenRatio_pos]; norm_num
    rw [this, Real.rpow_one]
    apply mulPos_contains_mul phi_pow_37_lo_pos phi_lo_pos h_in_37 h_in_1

  unfold phi_pow_140_interval
  have : goldenRatio ^ (140 : ℝ) = goldenRatio ^ (102 : ℝ) * goldenRatio ^ (38 : ℝ) := by
    rw [← Real.rpow_add goldenRatio_pos]; norm_num
  rw [this]
  apply mulPos_contains_mul phi_pow_102_lo_pos phi_pow_38_lo_pos h_in_102 h_in_38

theorem phi_pow_145_in_interval : phi_pow_145_interval.contains (goldenRatio ^ (145 : ℝ)) := by
  have h_in_140 := phi_pow_140_in_interval
  have h_in_5 : phi_pow_5_interval.contains (goldenRatio ^ (5 : ℝ)) := phi_pow_5_in_interval
  unfold phi_pow_145_interval
  have : goldenRatio ^ (145 : ℝ) = goldenRatio ^ (140 : ℝ) * goldenRatio ^ (5 : ℝ) := by
    rw [← Real.rpow_add goldenRatio_pos]; norm_num
  rw [this]
  apply mulPos_contains_mul phi_pow_140_lo_pos phi_pow_5_lo_pos h_in_140 h_in_5

/-- φ^140 < galactic_ratio -/
theorem phi_pow_140_lt_ratio : goldenRatio ^ (140 : ℝ) < (galactic_ratio_rational : ℝ) := by
  have h_in_140 := phi_pow_140_in_interval
  have h_hi : phi_pow_140_interval.hi < galactic_ratio_rational := by
    unfold phi_pow_140_interval phi_pow_102_interval phi_pow_38_interval phi_pow_37_interval phi_pow_32_interval phi_pow_51_interval phi_pow_16_interval phi_pow_5_interval phiInterval mulPos
    norm_num
  exact lt_of_le_of_lt h_in_140.2 (by exact_mod_cast h_hi)

/-- galactic_ratio < φ^145 -/
theorem ratio_lt_phi_pow_145 : (galactic_ratio_rational : ℝ) < goldenRatio ^ (145 : ℝ) := by
  have h_in_145 := phi_pow_145_in_interval
  have h_lo : galactic_ratio_rational < phi_pow_145_interval.lo := by
    unfold phi_pow_145_interval phi_pow_140_interval phi_pow_102_interval phi_pow_38_interval phi_pow_37_interval phi_pow_32_interval phi_pow_51_interval phi_pow_16_interval phi_pow_5_interval phiInterval mulPos
    norm_num
  exact lt_of_lt_of_le (by exact_mod_cast h_lo) h_in_145.1

/-- Interval for φ^2 = φ + 1 -/
def phi_pow_2_interval : Interval :=
  phiInterval.add (Interval.point 1)

lemma phi_pow_2_lo_pos : (0 : ℚ) < phi_pow_2_interval.lo := by
  unfold phi_pow_2_interval phiInterval; norm_num

/-- Interval for φ^142 = φ^140 * φ^2 -/
def phi_pow_142_interval : Interval :=
  mulPos phi_pow_140_interval phi_pow_2_interval phi_pow_140_lo_pos phi_pow_2_lo_pos

theorem phi_pow_142_in_interval : phi_pow_142_interval.contains (goldenRatio ^ (142 : ℝ)) := by
  have h_in_140 := phi_pow_140_in_interval
  have h_in_2 : phi_pow_2_interval.contains (goldenRatio ^ (2 : ℝ)) := by
    unfold phi_pow_2_interval
    have h_sq : goldenRatio ^ (2 : ℝ) = goldenRatio + 1 := goldenRatio_sq
    rw [h_sq]
    apply add_contains_add (phi_in_phiInterval) (contains_point 1)
  unfold phi_pow_142_interval
  have : goldenRatio ^ (142 : ℝ) = goldenRatio ^ (140 : ℝ) * goldenRatio ^ (2 : ℝ) := by
    rw [← Real.rpow_add goldenRatio_pos]; norm_num
  rw [this]
  apply mulPos_contains_mul phi_pow_140_lo_pos phi_pow_2_lo_pos h_in_140 h_in_2

theorem phi_pow_142_lt_ratio_1_3 : phi_pow_142_interval.hi < 13/10 * galactic_ratio_rational := by
  unfold phi_pow_142_interval phi_pow_2_interval phi_pow_140_interval phi_pow_102_interval phi_pow_38_interval phi_pow_37_interval phi_pow_32_interval phi_pow_51_interval phi_pow_16_interval phi_pow_5_interval phiInterval mulPos Interval.add Interval.point
  norm_num

theorem ratio_0_7_lt_phi_pow_142 : 7/10 * galactic_ratio_rational < phi_pow_142_interval.lo := by
  unfold phi_pow_142_interval phi_pow_2_interval phi_pow_140_interval phi_pow_102_interval phi_pow_38_interval phi_pow_37_interval phi_pow_32_interval phi_pow_51_interval phi_pow_16_interval phi_pow_5_interval phiInterval mulPos Interval.add Interval.point
  norm_num

end RecognitionScience.Numerics
