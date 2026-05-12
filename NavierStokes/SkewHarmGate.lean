import Mathlib

/-!
# Navier–Stokes “skew / harmonic tail” gate: Lean lemmas

This file is meant to support the two analytic steps that show up repeatedly in
`navier-dec-12-rewrite.tex`:

1. **Skew/self-adjoint cancellations** coming from integration by parts (no “bad boundary term”);
2. **Harmonic/affine tail mode bookkeeping**, where the only obstruction is a boundary term at
   infinity.

At the moment we formalize the *integration-by-parts / boundary-term* algebra cleanly.
The hard “tail decay ⇒ boundary term vanishes” is left as an explicit `Tendsto` hypothesis,
matching the TeX “bad tail violates Zero-Skew at infinity” language.
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes

open scoped Topology Interval BigOperators

open MeasureTheory Set

namespace Radial

/-!
## Weighted radial integration-by-parts identity

This packages the elementary identity behind TeX Remark “Energy identity behind the coercive
bound”:

Let `A` satisfy `A' = dA/dr` and `A'' = d²A/dr²`. Define `V(r) = r² A'(r)`. Then

`(-A''(r) - (2/r)A'(r)) A(r) r² = (-A(r)) * V'(r)`

so integration-by-parts yields an identity with a boundary term
`r² A(r) A'(r)` evaluated at the endpoints.
-/

section

variable {A A' A'' : ℝ → ℝ} {a b : ℝ}

private lemma hasDerivAt_rpow_two (r : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
  -- `d/dr (r^2) = 2r`
  simpa using ((hasDerivAt_id r).pow 2)

private lemma hasDerivAt_rsq_mul (x : ℝ)
    (hA' : HasDerivAt A' (A'' x) x) :
    HasDerivAt (fun t : ℝ => (t ^ 2) * (A' t)) ((2 * x) * (A' x) + (x ^ 2) * (A'' x)) x := by
  -- product rule for `(x^2) * A'(x)`
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := hasDerivAt_rpow_two (r := x)
  simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using hpow.mul hA'

end

/-!
### Finite-interval skew cancellation

This is the clean “no cross term” identity on a finite interval.
-/

section Finite

variable {A A' A'' : ℝ → ℝ} {R : ℝ}

lemma integral_radial_skew_identity
    (hR : 1 ≤ R)
    (hA : ∀ x ∈ Set.uIcc (1 : ℝ) R, HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Set.uIcc (1 : ℝ) R, HasDerivAt A' (A'' x) x)
    (hA'_int : IntervalIntegrable A' volume (1 : ℝ) R)
    (hV'_int :
      IntervalIntegrable (fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x)) volume (1 : ℝ) R) :
    (∫ x in (1 : ℝ)..R,
        (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2)) =
      (-(A R) * (R ^ 2 * A' R) + (A 1) * (1 ^ 2 * A' 1))
        + ∫ x in (1 : ℝ)..R, (A' x) ^ 2 * (x ^ 2) := by
  -- Apply integration by parts to `u = -A` and `v = (x^2)A'`.
  have hu :
      ∀ x ∈ Set.uIcc (1 : ℝ) R, HasDerivAt (fun y => -A y) (-(A' x)) x := by
    intro x hx
    simpa using (hA x hx).neg

  have hv :
      ∀ x ∈ Set.uIcc (1 : ℝ) R,
        HasDerivAt (fun y : ℝ => (y ^ 2) * (A' y))
          ((2 * x) * (A' x) + (x ^ 2) * (A'' x)) x := by
    intro x hx
    exact hasDerivAt_rsq_mul (A' := A') (A'' := A'') x (hA' x hx)

  -- The `IntervalIntegrable` hypothesis for `u'` is inherited from `A'`.
  have hu'_int : IntervalIntegrable (fun x : ℝ => -(A' x)) volume (1 : ℝ) R := by
    simpa using hA'_int.neg

  have hv'_int :
      IntervalIntegrable (fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x)) volume (1 : ℝ) R :=
    hV'_int

  -- Integration by parts.
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := R)
      (u := fun x => -A x) (v := fun x : ℝ => (x ^ 2) * (A' x))
      (u' := fun x => -(A' x))
      (v' := fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x))
      hu hv hu'_int hv'_int

  -- Rewrite the LHS into the TeX integrand, and simplify the RHS.
  -- `(-A) * v' = (-(A'' ) - (2/x) A') * A * x^2`
  -- and `-(u')*v = (A')*(x^2*A') = (A')^2*x^2`.
  -- Also simplify the boundary terms at `x=1` (note `1^2 = 1`, kept as-is for clarity).
  have : (∫ x in (1 : ℝ)..R, (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) =
      ∫ x in (1 : ℝ)..R, (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2) := by
    -- pointwise algebra inside the integral
    refine intervalIntegral.integral_congr ?_
    intro x hx
    -- hx : x ∈ Set.uIcc 1 R (so x ≠ 0); we only need algebra.
    have hx0 : x ≠ 0 := by
      -- since `1 ≤ R`, membership in `uIcc 1 R` implies `x ≥ 0` and in fact `x ≥ 1` or `x ≤ 1`;
      -- either way `x = 0` is impossible because `0 ∉ uIcc 1 R`.
      -- Use a simple order argument:
      have : x ∈ Set.Icc (min (1 : ℝ) R) (max (1 : ℝ) R) := by
        simpa [Set.uIcc] using hx
      have hxlo : min (1 : ℝ) R ≤ x := this.1
      -- `min 1 R ≤ x` and `min 1 R ≥ 0` hence `x ≠ 0` unless both are 0, impossible.
      have hminpos : 0 < min (1 : ℝ) R := by
        have : 0 < (1 : ℝ) := by norm_num
        have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
        -- `min 1 R` is positive since both are positive
        exact lt_min this hR0
      exact ne_of_gt (lt_of_lt_of_le hminpos hxlo)
    -- now just ring-ish simplification
    field_simp [hx0]
    ring

  -- Use the rewritten version of `hparts` and finish.
  -- Start from `hparts` and substitute the LHS.
  -- hparts:
  --   ∫ u * v' = u b * v b - u a * v a - ∫ u' * v
  -- for u=-A, v=x^2*A'.
  -- Move everything to match our target statement.
  -- We'll rewrite `∫ u' * v` and the boundary terms.
  calc
    (∫ x in (1 : ℝ)..R, (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2)) =
        (∫ x in (1 : ℝ)..R, (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) := by
          -- `this` was proved in the forward direction; use symmetry here.
          simpa using this.symm
    _ =
        (-A R) * ((R ^ 2) * (A' R))
          - (-A 1) * ((1 ^ 2) * (A' 1))
          - ∫ x in (1 : ℝ)..R, (-(A' x)) * ((x ^ 2) * (A' x)) := by
          simpa using hparts
    _ =
        (-(A R) * (R ^ 2 * A' R) + (A 1) * (1 ^ 2 * A' 1))
          + ∫ x in (1 : ℝ)..R, (A' x) ^ 2 * (x ^ 2) := by
          -- boundary terms + integral algebra
          -- First simplify signs in boundary terms.
          -- Then `- ∫ (-(A'))*(x^2*A') = + ∫ (A')*(x^2*A') = ∫ (A')^2 * x^2`.
          have h_int :
              -(∫ x in (1 : ℝ)..R, (-(A' x)) * (x ^ 2 * A' x)) =
                ∫ x in (1 : ℝ)..R, (A' x) ^ 2 * (x ^ 2) := by
            -- simplify under the integral
            simp [pow_two, mul_left_comm, mul_comm]
          -- Now rewrite the whole expression.
          -- We keep `1^2` explicit to mirror the TeX boundary term at r=1.
          -- Use `ring` for scalar algebra outside integrals.
          -- Note: `simp` won't rewrite `a - b - c` to `(-a*b + ...) + ...` automatically.
          -- We'll do it stepwise.
          -- Start: (-A R)*... - (-A 1)*... - integral
          -- = (-(A R)*...) + (A 1*...) + ( - integral )
          -- then substitute `h_int`.
          calc
            (-A R) * (R ^ 2 * A' R) - (-A 1) * (1 ^ 2 * A' 1)
                - ∫ x in (1 : ℝ)..R, (-(A' x)) * (x ^ 2 * A' x)
              =
                (-(A R) * (R ^ 2 * A' R) + (A 1) * (1 ^ 2 * A' 1))
                  + (-(∫ x in (1 : ℝ)..R, (-(A' x)) * (x ^ 2 * A' x))) := by
                ring
            _ =
                (-(A R) * (R ^ 2 * A' R) + (A 1) * (1 ^ 2 * A' 1))
                  + (∫ x in (1 : ℝ)..R, (A' x) ^ 2 * (x ^ 2)) := by
                -- reduce the second summand using `h_int`, then clean up the remaining algebra
                have hmul :
                    (∫ x in (1 : ℝ)..R, A' x * (x ^ 2 * A' x)) =
                      ∫ x in (1 : ℝ)..R, (A' x) ^ 2 * (x ^ 2) := by
                  -- pointwise: `A' * (x^2 * A') = (A')^2 * x^2`
                  refine intervalIntegral.integral_congr ?_
                  intro x hx
                  simp [pow_two, mul_left_comm, mul_comm]
                -- `h_int` rewrites the negated integral; then rewrite the remaining integral
                -- via `hmul`.
                simp [hmul]

end Finite

/-!
### Finite-interval skew cancellation (general lower cutoff)

This is the same identity as `integral_radial_skew_identity`, but on an interval `[a, R]`
with a general lower endpoint `a`. This is useful for RM2U-style arguments because the
radial coefficient PDE/ODE is naturally formulated on `(1, ∞)` and we may not want to
assume differentiability at `r = 1`.
-/

section FiniteFrom

variable {A A' A'' : ℝ → ℝ} {a R : ℝ}

lemma integral_radial_skew_identity_from
    (haR : a ≤ R)
    (ha0 : 0 < a)
    (hA : ∀ x ∈ Set.uIcc a R, HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Set.uIcc a R, HasDerivAt A' (A'' x) x)
    (hA'_int : IntervalIntegrable A' volume a R)
    (hV'_int :
      IntervalIntegrable (fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x)) volume a R) :
    (∫ x in a..R,
        (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2)) =
      (-(A R) * (R ^ 2 * A' R) + (A a) * (a ^ 2 * A' a))
        + ∫ x in a..R, (A' x) ^ 2 * (x ^ 2) := by
  -- Apply integration by parts to `u = -A` and `v = (x^2)A'`.
  have hu :
      ∀ x ∈ Set.uIcc a R, HasDerivAt (fun y => -A y) (-(A' x)) x := by
    intro x hx
    simpa using (hA x hx).neg

  have hv :
      ∀ x ∈ Set.uIcc a R,
        HasDerivAt (fun y : ℝ => (y ^ 2) * (A' y))
          ((2 * x) * (A' x) + (x ^ 2) * (A'' x)) x := by
    intro x hx
    exact hasDerivAt_rsq_mul (A' := A') (A'' := A'') x (hA' x hx)

  -- The `IntervalIntegrable` hypothesis for `u'` is inherited from `A'`.
  have hu'_int : IntervalIntegrable (fun x : ℝ => -(A' x)) volume a R := by
    simpa using hA'_int.neg

  -- Integration by parts.
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := R)
      (u := fun x => -A x) (v := fun x : ℝ => (x ^ 2) * (A' x))
      (u' := fun x => -(A' x))
      (v' := fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x))
      hu hv hu'_int hV'_int

  -- Rewrite the LHS into the TeX integrand, and simplify the RHS.
  have :
      (∫ x in a..R, (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) =
        ∫ x in a..R, (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc a R := by
      -- since `a ≤ R`, `uIcc a R = Icc a R`
      simpa [Set.uIcc_of_le haR] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hx'.1)
    field_simp [hx0]
    ring

  -- Finish as in `integral_radial_skew_identity`.
  calc
    (∫ x in a..R, (-(A'' x) - (2 / x) * (A' x)) * (A x) * (x ^ 2)) =
        (∫ x in a..R, (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) := by
          simpa using this.symm
    _ =
        (-A R) * ((R ^ 2) * (A' R))
          - (-A a) * ((a ^ 2) * (A' a))
          - ∫ x in a..R, (-(A' x)) * ((x ^ 2) * (A' x)) := by
          simpa using hparts
    _ =
        (-(A R) * (R ^ 2 * A' R) + (A a) * (a ^ 2 * A' a))
          + ∫ x in a..R, (A' x) ^ 2 * (x ^ 2) := by
          -- Keep the sign bookkeeping explicit to avoid simp rewriting the statement.
          have h_int :
              -(∫ x in a..R, (-(A' x)) * (x ^ 2 * A' x)) =
                ∫ x in a..R, (A' x) ^ 2 * (x ^ 2) := by
            have hneg :
                -(∫ x in a..R, (-(A' x)) * (x ^ 2 * A' x)) =
                  ∫ x in a..R, A' x * (x ^ 2 * A' x) := by
              -- `(-A') * (...)` is `-(A'*(...))`, so the outer `-` cancels.
              simp [neg_mul, intervalIntegral.integral_neg]
            have hmul :
                (∫ x in a..R, A' x * (x ^ 2 * A' x)) =
                  ∫ x in a..R, (A' x) ^ 2 * (x ^ 2) := by
              refine intervalIntegral.integral_congr ?_
              intro x hx
              simp [pow_two, mul_left_comm, mul_comm]
            exact hneg.trans hmul
          calc
            (-A R) * (R ^ 2 * A' R) - (-A a) * (a ^ 2 * A' a)
                - ∫ x in a..R, (-(A' x)) * (x ^ 2 * A' x)
              =
                (-(A R) * (R ^ 2 * A' R) + (A a) * (a ^ 2 * A' a))
                  + (-(∫ x in a..R, (-(A' x)) * (x ^ 2 * A' x))) := by
                ring
            _ =
                (-(A R) * (R ^ 2 * A' R) + (A a) * (a ^ 2 * A' a))
                  + (∫ x in a..R, (A' x) ^ 2 * (x ^ 2)) := by
                -- rewrite the last term using `h_int`
                exact congrArg
                  (fun t => (-(A R) * (R ^ 2 * A' R) + (A a) * (a ^ 2 * A' a)) + t) h_int

end FiniteFrom

/-!
### Improper-interval version (boundary term at ∞ explicit)

This is the direct Lean formalization of the “bad tail violates Zero-Skew at infinity” statement:
the only extra hypothesis needed to run the same integration-by-parts on `(1, ∞)` is a
`Tendsto (u*v) atTop (𝓝 b')` condition. Setting `b' = 0` is exactly the **Zero-Skew at infinity**
condition in this one-dimensional reduction.
-/

section Ioi

variable {A A' A'' : ℝ → ℝ} {a' b' : ℝ}

/-!
### Deriving the “Zero-Skew at infinity” condition from integrability

Mathlib already contains a very useful lemma:
`MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`.

In our setting, the *boundary term* is the scalar function

`B(r) := (-A(r)) * (r^2 * A'(r))`.

If `B` and `B'` are integrable on `(1,∞)`, then `B(r) → 0` as `r → ∞`.
This is precisely the Lean form of “Zero-Skew at infinity”.
-/

lemma zeroSkewAtInfinity_of_integrable
    (hA : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A' (A'' x) x)
    (hB_int :
      IntegrableOn (fun x : ℝ => (-A x) * ((A' x) * (x ^ 2))) (Set.Ioi (1 : ℝ)) volume)
    (hB'_int :
      IntegrableOn
        (fun x : ℝ =>
          (-(A' x)) * ((A' x) * (x ^ 2)) + (-A x) * ((A'' x) * (x ^ 2) + (A' x) * (2 * x)))
        (Set.Ioi (1 : ℝ)) volume) :
    Filter.Tendsto (fun x : ℝ => (-A x) * ((A' x) * (x ^ 2))) Filter.atTop (𝓝 0) := by
  -- Use the Mathlib lemma with `f = (-A) * (x^2*A')`.
  have hderiv :
      ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivAt (fun x : ℝ => (-A x) * ((A' x) * (x ^ 2)))
          ((-(A' x)) * ((A' x) * (x ^ 2)) + (-A x) * ((A'' x) * (x ^ 2) + (A' x) * (2 * x))) x := by
    intro x hx
    have hu : HasDerivAt (fun y => -A y) (-(A' x)) x := by
      simpa using (hA x hx).neg
    have hv : HasDerivAt (fun y : ℝ => (A' y) * (y ^ 2)) ((A'' x) * (x ^ 2) + (A' x) * (2 * x)) x := by
      have hA'x : HasDerivAt A' (A'' x) x := hA' x hx
      have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := hasDerivAt_rpow_two (r := x)
      -- product rule for `A'(y) * y^2`
      simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using hA'x.mul hpow
    -- product rule
    simpa [Pi.mul_def, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hu.mul hv

  -- Now apply `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` on `(1,∞)`.
  simpa using
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := (1 : ℝ))
      (f := fun x : ℝ => (-A x) * ((A' x) * (x ^ 2)))
      (f' := fun x : ℝ =>
        (-(A' x)) * ((A' x) * (x ^ 2)) + (-A x) * ((A'' x) * (x ^ 2) + (A' x) * (2 * x)))
      hderiv hB'_int hB_int

lemma integral_Ioi_radial_skew_identity
    (hA : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A' (A'' x) x)
    (hUV' :
      IntegrableOn
        (fun x : ℝ => (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x)))
        (Set.Ioi (1 : ℝ)) volume)
    (hU'V :
      IntegrableOn
        (fun x : ℝ => (-(A' x)) * ((x ^ 2) * (A' x)))
        (Set.Ioi (1 : ℝ)) volume)
    -- Boundary terms: right-limit at `1` and limit at infinity.
    (h_zero :
      Filter.Tendsto
        (fun x : ℝ => (-A x) * ((x ^ 2) * (A' x)))
        (𝓝[>] (1 : ℝ)) (𝓝 a'))
    (h_infty :
      Filter.Tendsto
        (fun x : ℝ => (-A x) * ((x ^ 2) * (A' x)))
        Filter.atTop (𝓝 b')) :
    (∫ x in Set.Ioi (1 : ℝ), (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) =
      b' - a' + ∫ x in Set.Ioi (1 : ℝ), (A' x) ^ 2 * (x ^ 2) := by
  -- Apply `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` to
  --   u = -A,  u' = -A'
  --   v = x^2 * A', v' = 2*x*A' + x^2*A''
  have hu : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt (fun y => -A y) (-(A' x)) x := by
    intro x hx
    simpa using (hA x hx).neg

  have hv :
      ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivAt (fun y : ℝ => (y ^ 2) * (A' y))
          ((2 * x) * (A' x) + (x ^ 2) * (A'' x)) x := by
    intro x hx
    exact hasDerivAt_rsq_mul (A' := A') (A'' := A'') x (hA' x hx)

  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (A := ℝ) (a := (1 : ℝ))
      (a' := a') (b' := b')
      (u := fun x => -A x)
      (v := fun x : ℝ => (x ^ 2) * (A' x))
      (u' := fun x => -(A' x))
      (v' := fun x : ℝ => (2 * x) * (A' x) + (x ^ 2) * (A'' x))
      hu hv hUV' hU'V (by simpa [Pi.mul_def] using h_zero) (by simpa [Pi.mul_def] using h_infty)

  -- `hparts` gives: ∫ u*v' = b' - a' - ∫ u'*v.
  -- Simplify `-∫ (-(A'))*(x^2*A')` into `+∫ (A')^2*x^2`.
  -- (We keep the overall sign convention aligned with the TeX remark.)
  have hneg :
      -(∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x))) =
        ∫ x in Set.Ioi (1 : ℝ), (A' x) ^ 2 * (x ^ 2) := by
    -- `-(∫ -(A'*(x^2*A'))) = ∫ A'*(x^2*A') = ∫ (A')^2*x^2`
    -- First pull the negation out of the integral.
    -- Then simplify the integrand pointwise.
    have :
        -(∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x))) =
          ∫ x in Set.Ioi (1 : ℝ), A' x * ((x ^ 2) * (A' x)) := by
      -- `(-A') * (...) = -(A'*(...))`, so the inner integral is `-∫ A'*(...)`,
      -- and the outer `-` cancels it.
      simp [neg_mul, MeasureTheory.integral_neg]
    -- Now use the pointwise algebra `A' * (x^2 * A') = (A')^2 * x^2`.
    -- (Associativity/commutativity is handled by `simp`.)
    calc
      -(∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x))) =
          ∫ x in Set.Ioi (1 : ℝ), A' x * ((x ^ 2) * (A' x)) := this
      _ = ∫ x in Set.Ioi (1 : ℝ), (A' x) ^ 2 * (x ^ 2) := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          simp [pow_two, mul_left_comm, mul_comm]

  -- Finish.
  -- From hparts: LHS = b' - a' - ∫ u'*v.
  -- Replace the `- ∫ u'*v` term using `hneg`.
  calc
    (∫ x in Set.Ioi (1 : ℝ), (-A x) * ((2 * x) * (A' x) + (x ^ 2) * (A'' x))) =
        b' - a' - ∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x)) := by
          simpa using hparts
    _ = b' - a' + ∫ x in Set.Ioi (1 : ℝ), (A' x) ^ 2 * (x ^ 2) := by
          -- rewrite the last term using `hneg`
          -- `b' - a' - I = b' - a' + (-I)`
          -- Avoid `simp` turning `(-A')*(x^2*A')` into `-(A'*(x^2*A'))` so that we can use `hneg`.
          calc
            b' - a' - ∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x)) =
                b' - a' + (-(∫ x in Set.Ioi (1 : ℝ), (-(A' x)) * ((x ^ 2) * (A' x)))) := by
                  ring
            _ = b' - a' + ∫ x in Set.Ioi (1 : ℝ), (A' x) ^ 2 * (x ^ 2) := by
                  -- Use `hneg` as a rewrite without letting `simp` normalize the integrand.
                  simpa using congrArg (fun t => b' - a' + t) hneg

end Ioi

end Radial

end NavierStokes
-- end IndisputableMonolith
