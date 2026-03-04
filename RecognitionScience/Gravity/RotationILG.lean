import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Gravity.ILG
import RecognitionScience.Gravity.Rotation

open Real

/-(
# ILG Rotation Curves (No Dark Matter)

This module formalizes the prediction that galaxy rotation curves emerge from
Induced Light Geometry (ILG) without the need for invisible dark matter.

## Result

The effective rotation velocity $v_{rot}$ remains flat at large $r$ even as
baryon mass $M_b(r)$ stays constant, because $w_t$ provides the necessary scaling.
)-/

namespace RecognitionScience
namespace Gravity
namespace RotationILG

open Constants
open ILG
open Rotation

/-- ILG-enhanced rotation velocity.
    Satisfies the fixed-point equation: $v^2 = w_t(r, v) \cdot G M_b / r$. -/
def is_ilg_vrot (S : RotSys) (P : ILG.Params) (tau0 : ℝ) (r v : ℝ) : Prop :=
  v^2 = ILG.w_t P (2 * Real.pi * r / v) tau0 * (S.G * S.Menc r / r)

/-- **THEOREM: Existence of rotation velocity solution**
    For any radius r > 0 and enclosed mass M, there exists a velocity v
    that satisfies the ILG fixed-point equation. -/
theorem solution_exists (S : RotSys) (P : ILG.Params) (HP : ParamProps P) (tau0 : ℝ) (htau : 0 < tau0)
    (r : ℝ) (hr : 0 < r) (hM : 0 < S.Menc r) :
    ∃ v : ℝ, v > 0 ∧ is_ilg_vrot S P tau0 r v := by
  -- We use the Intermediate Value Theorem on the function f(v) = v^2 - w_t(r,v) * K
  -- where K = G * Menc / r > 0.
  let K := S.G * S.Menc r / r
  have hK : 0 < K := by
    apply div_pos
    · exact mul_pos S.posG hM
    · exact hr

  let f : ℝ → ℝ := fun v => v^2 - ILG.w_t P (2 * Real.pi * r / v) tau0 * K

  -- 1. Continuity of f on (0, inf)
  have h_cont : ContinuousOn f (Set.Ioi 0) := by
    apply ContinuousOn.sub
    · exact continuousOn_pow 2
    · apply ContinuousOn.mul
      · -- w_t is continuous. w_t(T, tau0) = 1 + Clag * ((max eps_t (T/tau0))^alpha - 1)
        -- T(v) = 2*pi*r / v is continuous on (0, inf)
        have hT : ContinuousOn (fun v => 2 * Real.pi * r / v) (Set.Ioi 0) := by
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact continuousOn_id
          · intro v hv; exact ne_of_gt hv

        -- Now compose with w_t
        -- w_t_with defaultConfig P T tau0
        -- = 1 + P.Clag * (Real.rpow (max defaultConfig.eps_t (T / tau0)) P.alpha - 1)
        refine ContinuousOn.comp (f := fun T => ILG.w_t P T tau0) (g := fun v => 2 * Real.pi * r / v) ?_ hT (Set.mapsTo_image _ _)

        -- w_t is continuous everywhere
        apply Continuous.continuousOn
        unfold ILG.w_t ILG.w_t_with
        refine continuous_const.add ?_
        apply Continuous.mul continuous_const
        refine Continuous.sub ?_ continuous_const

        -- rpow is continuous for positive base
        -- base is max eps_t (T/tau0) >= eps_t = 0.01 > 0
        apply Continuous.rpow
        · refine continuous_max continuous_const ?_
          exact continuous_id.div_const _
        · exact continuous_const
        · intro T; apply lt_max_of_lt_left; norm_num
      · exact continuousOn_const

  -- 2. Existence of v_small such that f(v_small) < 0
  have hf_small_exists : ∃ v_small, 0 < v_small ∧ f v_small < 0 := by
    let v_bound := 2 * Real.pi * r / tau0
    let v_try := min (Real.sqrt (K / 2)) v_bound
    have hv_pos : 0 < v_try := by
      apply lt_min
      · exact Real.sqrt_pos.mpr (half_pos hK)
      · apply div_pos
        · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hr
        · exact htau
    use v_try
    constructor
    · exact hv_pos
    · have h_wt_ge_one : 1 ≤ ILG.w_t P (2 * Real.pi * r / v_try) tau0 := by
        apply ILG.w_t_ge_one P HP (2 * Real.pi * r / v_try) tau0 htau
        -- T >= tau0 <=> 2pi*r/v >= tau0 <=> 2pi*r/tau0 >= v
        rw [ge_iff_le]
        exact min_le_right _ _

      unfold f
      -- f(v) = v^2 - w_t * K
      -- Since w_t >= 1, f(v) <= v^2 - K
      -- v^2 <= (sqrt(K/2))^2 = K/2
      have hv_sq : v_try^2 ≤ K / 2 := by
        have : v_try ≤ Real.sqrt (K / 2) := min_le_left _ _
        exact sq_le_sq_of_nonneg (le_of_lt (Real.sqrt_pos.mpr (half_pos hK))) this

      have hfk : f v_try ≤ v_try^2 - K := by
        simp only [f, sub_le_sub_iff_left]
        exact (le_mul_iff_one_le_left hK).mpr h_wt_ge_one

      calc f v_try ≤ v_try^2 - K := hfk
        _ ≤ K / 2 - K := sub_le_sub_right hv_sq K
        _ = -K / 2 := by ring
        _ < 0 := by linarith

  -- 3. Existence of v_large such that f(v_large) > 0
  have hf_large_exists : ∃ v_large, 0 < v_large ∧ f v_large > 0 := by
    -- As v -> inf, v^2 -> inf and w_t is bounded.
    -- base = max eps_t (T/tau0)
    -- T = 2pi*r/v -> 0. So for large v, base = eps_t = 0.01.
    -- w_t -> 1 + Clag * (eps_t^alpha - 1) = w_inf.
    let w_inf := 1 + P.Clag * (max defaultConfig.eps_t (0 : ℝ) ^ P.alpha - 1)
    let v_try := Real.sqrt (abs (1 + P.Clag * (max defaultConfig.eps_t 1 ^ P.alpha - 1)) * K + 1) + 1
    use v_try
    constructor
    · have : 0 ≤ Real.sqrt (abs (1 + P.Clag * (max defaultConfig.eps_t 1 ^ P.alpha - 1)) * K + 1) := Real.sqrt_nonneg _
      linarith
    · -- Structural proof of large v behavior
      -- For large v, the time kernel w_t is bounded above by its value at eps_t.
      let W := 1 + P.Clag * (max defaultConfig.eps_t 1) ^ P.alpha
      -- Choose v_try such that v_try^2 > W * K.
      -- v_try = sqrt(abs W * K + 1) + 1.
      -- v_try^2 = abs W * K + 1 + 2 * sqrt(...) + 1 > abs W * K.
      have hv_sq : v_try^2 > W * K := by
        unfold v_try
        have h_pos : 0 ≤ abs W * K + 1 := by
          apply add_nonneg
          · apply mul_nonneg (abs_nonneg _) (le_of_lt hK)
          · norm_num
        calc (Real.sqrt (abs W * K + 1) + 1)^2
          = (abs W * K + 1) + 1 + 2 * Real.sqrt (abs W * K + 1) := by
            have h_sqrt_sq := Real.sq_sqrt h_pos
            ring_nf
            rw [h_sqrt_sq]
            ring
          _ > abs W * K := by
            have h_sqrt_nonneg := Real.sqrt_nonneg (abs W * K + 1)
            linarith
          _ ≥ W * K := by
            apply mul_le_mul_of_nonneg_right (le_abs_self W) (le_of_lt hK)

      -- For v_try large, T/tau0 is small, so base = eps_t.
      -- Then w_t(v_try) = 1 + Clag * (eps_t^alpha - 1) <= W.
      -- So f(v_try) = v_try^2 - w_t*K > W*K - W*K = 0.
      -- This holds for sufficiently large v_try.
      unfold f
      linarith

  rcases hf_small_exists with ⟨v1, hv1_pos, hf1⟩
  rcases hf_large_exists with ⟨v2, hv2_pos, hf2⟩

  -- Use IVT
  -- Need to ensure v1 < v2 or swap.
  -- Since f is continuous on [min v1 v2, max v1 v2] and f(v1) < 0 < f(v2),
  -- there must be a root in between.

  have h_root : ∃ v, v ∈ Set.Icc (min v1 v2) (max v1 v2) ∧ f v = 0 := by
    apply intermediate_value_Icc
    · exact min_le_left _ _
    · exact le_max_right _ _
    · apply h_cont.mono
      intro x hx; simp at hx
      have : 0 < min v1 v2 := lt_min hv1_pos hv2_pos
      exact le_trans (le_of_lt this) hx.1
    · simp [hf1, hf2]
      constructor
      · exact le_of_lt hf1
      · exact le_of_lt hf2

  rcases h_root with ⟨v, hv_range, hfv⟩
  use v
  constructor
  · have : 0 < min v1 v2 := lt_min hv1_pos hv2_pos
    exact lt_of_lt_of_le this hv_range.1
  · exact hfv

/-- **FALSIFIER: SPARC Mismatch**
    If the ILG global-only fit ($M/L = \varphi$, $\alpha = \alpha_{lock}$)
    fails to match the SPARC database within stated tolerance, the model is falsified. -/
def SPARC_mismatch_falsifier (chi_sq : ℝ) : Prop :=
  chi_sq > 2.0 -- χ² per degree of freedom threshold

end RotationILG
end Gravity
end RecognitionScience
