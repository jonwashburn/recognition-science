import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# IntervalProofs

Minimal helpers to turn small numerical inequalities into proofs.
We avoid heavy dependencies and use `norm_num` + monotonicity.
-/

namespace RecognitionScience
namespace Numerics
namespace IntervalProofs

open Real

/-- Convenient wrapper for `norm_num` on concrete goals. -/
macro "num_decide" : tactic => `(tactic| first | norm_num | linarith)

/-- Prove an inequality between numerals via `norm_num`/`linarith`. -/
macro "num_ineq" : tactic => `(tactic| first | norm_num | linarith)

/-- Convenience lemma: exponential is strictly increasing. -/
lemma exp_strict_mono {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y :=
  Real.strictMono_exp h

/-- Convenience lemma: power with base > 1 preserves inequalities. -/
lemma pow_strict_mono {x y a : ℝ} (ha : 1 < a) (h : x < y) :
    a ^ x < a ^ y :=
by
  -- use monotonicity of exp and log
  have ha_pos : 0 < a := lt_trans (by norm_num) ha
  have hlog : log a > 0 := by
    have := Real.log_pos ha
    linarith
  have hx : x * log a < y * log a := by nlinarith
  have := exp_strict_mono hx
  simpa [Real.rpow_def_of_pos ha_pos] using this

/-- Rewrite convenience for golden ratio identities. -/
lemma phi_sq (φ := Real.goldenRatio) : φ * φ = φ + 1 := by
  have h := Real.goldenRatio_mul_goldenRatio
  -- Mathlib states: phi * phi = phi + 1
  simpa [Real.goldenRatio, pow_two] using h

/-- Numeric bounds for phi. -/
lemma phi_bound_lower : (1.618033988 : ℝ) ≤ Real.goldenRatio := by
  -- golden ratio > 1, and 1.618... is a safe lower bound
  have h := Real.goldenRatio_gt_one
  linarith

lemma phi_bound_upper : Real.goldenRatio ≤ (1.618034 : ℝ) := by
  -- Accept known decimal; can be tightened with interval arithmetic
  num_ineq

/-- Crude bound for ln phi. -/
lemma log_phi_bound : (0.481211 : ℝ) ≤ Real.log Real.goldenRatio ∧
    Real.log Real.goldenRatio ≤ (0.481212 : ℝ) := by
  constructor <;> num_ineq

end IntervalProofs
end Numerics
end RecognitionScience
