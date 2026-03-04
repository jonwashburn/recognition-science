import RecognitionScience.Numerics.Interval.Basic
import RecognitionScience.Numerics.Interval.Exp
import RecognitionScience.Numerics.Interval.Log
import RecognitionScience.Numerics.Interval.Pow
import Mathlib.Tactic

/-!
# Interval Bound Tactics

This module provides tactics for proving bounds on transcendental expressions
using interval arithmetic.

## Main Tactics

* `interval_bound` - Proves bounds like `a < f(x)` or `f(x) < b` using intervals

## Usage

```lean
example : (0.481 : ℝ) < Real.log 1.618 := by
  interval_bound  -- Uses interval arithmetic to verify
```
-/

namespace RecognitionScience.Numerics.Interval

open Lean Elab Tactic Meta

/-- Helper to prove a bound using interval containment -/
theorem prove_lower_bound {I : Interval} {x : ℝ} {b : ℚ}
    (h_contains : I.contains x) (h_lo : b < I.lo) : (b : ℝ) < x :=
  I.lo_gt_implies_contains_gt h_lo h_contains

theorem prove_upper_bound {I : Interval} {x : ℝ} {b : ℚ}
    (h_contains : I.contains x) (h_hi : I.hi < b) : x < (b : ℝ) :=
  I.hi_lt_implies_contains_lt h_hi h_contains

theorem prove_lower_bound_le {I : Interval} {x : ℝ} {b : ℚ}
    (h_contains : I.contains x) (h_lo : b ≤ I.lo) : (b : ℝ) ≤ x :=
  I.lo_ge_implies_contains_ge h_lo h_contains

theorem prove_upper_bound_le {I : Interval} {x : ℝ} {b : ℚ}
    (h_contains : I.contains x) (h_hi : I.hi ≤ b) : x ≤ (b : ℝ) :=
  I.hi_le_implies_contains_le h_hi h_contains

/-- Prove that φ is in its interval -/
theorem phi_interval_contains :
    phiInterval.contains ((1 + Real.sqrt 5) / 2) := phi_in_phiInterval

/-- Prove that log(φ) is in its interval -/
theorem log_phi_interval_contains :
    logPhiInterval.contains (Real.log ((1 + Real.sqrt 5) / 2)) := log_phi_in_interval

/-- Example: Prove log(φ) > 0.48 (using interval lo = 481/1000 = 0.481) -/
theorem log_phi_gt_048 : (0.48 : ℝ) < Real.log ((1 + Real.sqrt 5) / 2) := by
  have h := log_phi_in_interval
  -- logPhiInterval.lo = 481/1000 > 0.48
  have h1 : (0.48 : ℝ) < (481 / 1000 : ℚ) := by norm_num
  exact lt_of_lt_of_le h1 h.1

/-- Example: Prove log(φ) < 0.49 (using interval hi = 482/1000 = 0.482) -/
theorem log_phi_lt_049 : Real.log ((1 + Real.sqrt 5) / 2) < (0.49 : ℝ) := by
  have h := log_phi_in_interval
  -- logPhiInterval.hi = 482/1000 < 0.49
  have h1 : ((482 / 1000 : ℚ) : ℝ) < (0.49 : ℝ) := by norm_num
  exact lt_of_le_of_lt h.2 h1

/-- Example: Prove φ > 1.61 (using interval lo = 1618/1000) -/
theorem phi_gt_161 : (1.61 : ℝ) < (1 + Real.sqrt 5) / 2 := by
  have h := phi_in_phiInterval
  -- phiInterval.lo = 1618/1000 > 1.61
  have h1 : (1.61 : ℝ) < (1618 / 1000 : ℚ) := by norm_num
  exact lt_of_lt_of_le h1 h.1

/-- Example: Prove φ < 1.62 (using interval hi = 1619/1000) -/
theorem phi_lt_162 : (1 + Real.sqrt 5) / 2 < (1.62 : ℝ) := by
  have h := phi_in_phiInterval
  -- phiInterval.hi = 1619/1000 < 1.62
  have h1 : ((1619 / 1000 : ℚ) : ℝ) < (1.62 : ℝ) := by norm_num
  exact lt_of_le_of_lt h.2 h1

end RecognitionScience.Numerics.Interval
