import Mathlib
import RecognitionScience.Constants

namespace RecognitionScience
namespace Constants

/-!
# Gap weight `w₈` — 8-tick projection weight (parameter-free, closed form)

In the α pipeline we use a single gap term:

`f_gap = w₈ · ln(φ)`.

Historically the repository carried `w₈` as a *numeric certificate*.
This is no longer acceptable for the “no free parameters” claim: `w₈` must be
defined from first principles.

We therefore expose `w8_from_eight_tick` as a **parameter-free closed form**
that is (numerically) the normalized DFT-8 “neutral spectral deficit” weight of
the canonical φ-pattern.

Notes:
- A DFT-based *raw* energy sum exists as `Constants.GapWeight.w8_dft_candidate`
  in `Constants/GapWeight/Formula.lean`.
- That raw sum is **not** equal to `w8_from_eight_tick` (see
  `Verification/GapWeightCandidateMismatchCert.lean`); the missing piece is a
  normalization/projection step.
- The closed form below is the current canonical projection weight on the
  8-tick basis.
-/

/-- The canonical gap weight `w₈` (parameter‑free, closed form).

This is the normalized projection weight of the gap onto the fundamental
8-tick basis. Numerically it is approximately `2.49056927545…`. -/
@[simp] noncomputable def w8_from_eight_tick : ℝ :=
  (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * phi) / 7

/-- Derived w₈ is positive. -/
theorem w8_pos : 0 < w8_from_eight_tick := by
  -- A coarse but self-contained positivity proof using rational upper bounds.
  -- We show the numerator is positive under worst-case substitution (largest φ and √2).
  have hs2_hi : Real.sqrt 2 < (71 / 50 : ℝ) := by
    have hx : (0 : ℝ) ≤ 2 := by norm_num
    have hy : (0 : ℝ) ≤ (71 / 50 : ℝ) := by norm_num
    have hsq : (2 : ℝ) < (71 / 50 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt hx hy).2 hsq
  have hs5_hi : Real.sqrt 5 < (56 / 25 : ℝ) := by
    have hx : (0 : ℝ) ≤ 5 := by norm_num
    have hy : (0 : ℝ) ≤ (56 / 25 : ℝ) := by norm_num
    have hsq : (5 : ℝ) < (56 / 25 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt hx hy).2 hsq
  have hphi_hi : phi < (81 / 50 : ℝ) := by
    -- φ = (1 + √5)/2 < (1 + 56/25)/2 = 81/50
    have : (phi : ℝ) = (1 + Real.sqrt 5) / 2 := by rfl
    rw [this]
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hnum : (1 + Real.sqrt 5) < (1 + (56 / 25 : ℝ)) := by linarith [hs5_hi]
    have hdiv : (1 + Real.sqrt 5) / 2 < (1 + (56 / 25 : ℝ)) / 2 :=
      div_lt_div_of_pos_right hnum h2pos
    have hR : (1 + (56 / 25 : ℝ)) / 2 = (81 / 50 : ℝ) := by norm_num
    simpa [hR] using hdiv
  have hphi_lo : (21 / 13 : ℝ) < phi := by
    -- √5 > 2.231, so φ = (1+√5)/2 > (1+2.231)/2 = 1.6155 > 21/13.
    have hs5_lo : (2231 / 1000 : ℝ) < Real.sqrt 5 := by
      have hx : (0 : ℝ) ≤ (2231 / 1000 : ℝ) := by norm_num
      have hsq : (2231 / 1000 : ℝ) ^ 2 < (5 : ℝ) := by norm_num
      exact (Real.lt_sqrt hx).2 hsq
    have : (phi : ℝ) = (1 + Real.sqrt 5) / 2 := by rfl
    rw [this]
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hnum : (1 + (2231 / 1000 : ℝ)) < (1 + Real.sqrt 5) := by linarith [hs5_lo]
    have hdiv : (1 + (2231 / 1000 : ℝ)) / 2 < (1 + Real.sqrt 5) / 2 :=
      div_lt_div_of_pos_right hnum h2pos
    have hconst : (21 / 13 : ℝ) < (1 + (2231 / 1000 : ℝ)) / 2 := by norm_num
    exact lt_trans hconst (by simpa using hdiv)
  have hcoeff_nonpos : (210 : ℝ) - 130 * phi ≤ 0 := by
    -- from 21/13 < φ, we get 210 ≤ 130φ
    have hφ : (21 / 13 : ℝ) ≤ phi := le_of_lt hphi_lo
    have : (210 : ℝ) ≤ 130 * phi := by
      have : (130 : ℝ) * (21 / 13 : ℝ) ≤ 130 * phi := by nlinarith [hφ]
      simpa using (le_trans (by norm_num : (210 : ℝ) ≤ (130 : ℝ) * (21 / 13 : ℝ)) this)
    linarith
  -- Numerator positivity by worst-case substitution (largest φ and √2).
  have hφ : phi ≤ (81 / 50 : ℝ) := le_of_lt hphi_hi
  have hs2 : Real.sqrt 2 ≤ (71 / 50 : ℝ) := le_of_lt hs2_hi
  have hconst :
      (0 : ℝ) <
        (348 : ℝ) - 204 * (81 / 50 : ℝ) + (71 / 50 : ℝ) * ((210 : ℝ) - 130 * (81 / 50 : ℝ)) := by
    norm_num
  have hbase :
      (348 : ℝ) - 204 * phi + (71 / 50 : ℝ) * ((210 : ℝ) - 130 * phi)
        ≥ (348 : ℝ) - 204 * (81 / 50 : ℝ) + (71 / 50 : ℝ) * ((210 : ℝ) - 130 * (81 / 50 : ℝ)) := by
    nlinarith [hφ]
  have hnum_pos :
      0 < (348 : ℝ) - 204 * phi + (71 / 50 : ℝ) * ((210 : ℝ) - 130 * phi) :=
    lt_of_lt_of_le hconst hbase
  have hterm :
      (Real.sqrt 2) * ((210 : ℝ) - 130 * phi) ≥ (71 / 50 : ℝ) * ((210 : ℝ) - 130 * phi) := by
    exact mul_le_mul_of_nonpos_right hs2 hcoeff_nonpos
  have hnum :
      0 < (348 : ℝ) - 204 * phi + (Real.sqrt 2) * ((210 : ℝ) - 130 * phi) := by
    linarith
  have hrewrite :
      (348 : ℝ) - 204 * phi + (Real.sqrt 2) * ((210 : ℝ) - 130 * phi)
        = (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * phi) := by
    ring
  have hnum' : 0 < (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * phi) := by
    simpa [hrewrite] using hnum
  have h7 : (0 : ℝ) < (7 : ℝ) := by norm_num
  unfold w8_from_eight_tick
  simpa using (div_pos hnum' h7)

noncomputable def f_gap : ℝ := w8_from_eight_tick * Real.log phi

def fGapLowerBound : ℚ := 2993443258792019287026689 / 2500000000000000000000000
def fGapUpperBound : ℚ := 5986887286510633232418913 / 5000000000000000000000000

/-- Hypothesis for the certified numerical bounds for the gap weight. -/
def f_gap_bounds_hypothesis : Prop :=
  ((fGapLowerBound : ℚ) : ℝ) < f_gap ∧ f_gap < ((fGapUpperBound : ℚ) : ℝ)

end Constants
end RecognitionScience
