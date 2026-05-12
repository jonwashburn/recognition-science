import NavierStokes.RM2U.Core
import NavierStokes.SkewHarmGate

/-!
# RM2U.EnergyIdentity

This file is the “algebraic spine” of Option A:

1. Define the tail-flux boundary term (already in `RM2U.Core`).
2. Use the already-proved lemma in `SkewHarmGate` to reduce
   “tail flux vanishes at infinity” to **two integrability obligations**
   for the boundary term and its derivative.

This keeps RM2U in a form that is:
- faithful to the manuscript, and
- maximally friendly to Lean / proof hygiene (no hidden assumptions).
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes
namespace RM2U

open Filter MeasureTheory Set
open scoped Topology Interval

/-!
## RM2U operator and finite-window energy identity (time-slice)

The TeX manuscript (Remark `rem:Ab-energy-identity`) uses the projected radial operator
\[
  \mathcal{L}A := -\partial_r^2 A - \frac{2}{r}\partial_r A + \frac{6}{r^2}A
\]
to obtain the coercive terms
\[
  \int |A_r|^2 r^2 + 6\int |A|^2.
\]

In Lean we do not yet formalize the full PDE-in-time; however, the *radial integration-by-parts*
piece is purely algebraic and can already be stated cleanly on any finite interval `[a, R]`
with `1 < a ≤ R`.
-/

/-- The RM2U “ℓ=2” radial operator (time-slice, no time derivative / forcing packaged here). -/
noncomputable def rm2uOp (P : RM2URadialProfile) (r : ℝ) : ℝ :=
  (-(P.A'' r) - (2 / r) * (P.A' r) + (6 / (r ^ 2)) * (P.A r))

/-- **Algebraic identity (Bet 1 derivative rewrite).**

The Bet‑1 “boundary term derivative” integrand can be rewritten (for `r ≠ 0`) as the RM2U operator
pairing minus the coercive nonnegative terms.

This is useful because it eliminates `A''` from the integrability surface: instead of proving
integrability of an expression involving `A''`, it suffices to control the pairing
`(rm2uOp P) * A * r^2` plus the already-coercive terms `A'^2*r^2` and `A^2`. -/
theorem bet1_boundaryTerm_deriv_integrand_eq
    (P : RM2URadialProfile) {r : ℝ} (hr : r ≠ 0) :
    (-(P.A' r)) * ((P.A' r) * (r ^ 2))
        + (-P.A r) * ((P.A'' r) * (r ^ 2) + (P.A' r) * (2 * r))
      =
      (rm2uOp P r) * (P.A r) * (r ^ 2)
        - (P.A' r) ^ 2 * (r ^ 2)
        - 6 * (P.A r) ^ 2 := by
  -- Expand `rm2uOp` and clear denominators (`r ≠ 0` on the RM2U domain `(1,∞)`).
  simp [rm2uOp]
  field_simp [hr]
  ring

/-- Finite-window coercive identity for the RM2U operator, with explicit boundary terms.

This is the precise Lean analogue of the integration-by-parts step inside
TeX Remark `rem:Ab-energy-identity`, but on `[a,R]` with `1 < a ≤ R`.

No PDE content is used here; this is just calculus + the already-formalized skew identity.
-/
theorem integral_rm2uOp_mul_energy_identity
    (P : RM2URadialProfile) {a R : ℝ}
    (ha1 : 1 < a) (haR : a ≤ R)
    (hA'_int : IntervalIntegrable P.A' volume a R)
    (hV'_int :
      IntervalIntegrable (fun x : ℝ => (2 * x) * (P.A' x) + (x ^ 2) * (P.A'' x)) volume a R)
    (hf :
      IntervalIntegrable
        (fun x : ℝ => (-(P.A'' x) - (2 / x) * (P.A' x)) * (P.A x) * (x ^ 2)) volume a R)
    (hg :
      IntervalIntegrable
        (fun x : ℝ => ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)) volume a R) :
    (∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)) =
      (-(P.A R) * (R ^ 2 * P.A' R) + (P.A a) * (a ^ 2 * P.A' a))
        + (∫ x in a..R, (P.A' x) ^ 2 * (x ^ 2))
        + 6 * (∫ x in a..R, (P.A x) ^ 2) := by
  -- First apply the skew identity to the `-(A'')-(2/r)A'` part.
  have hskew :
      (∫ x in a..R,
          (-(P.A'' x) - (2 / x) * (P.A' x)) * (P.A x) * (x ^ 2)) =
        (-(P.A R) * (R ^ 2 * P.A' R) + (P.A a) * (a ^ 2 * P.A' a))
          + ∫ x in a..R, (P.A' x) ^ 2 * (x ^ 2) := by
    -- Supply derivative hypotheses on `[a,R]` from the profile hypotheses on `(1,∞)`.
    have ha0 : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1) ha1
    have hA_on : ∀ x ∈ Set.uIcc a R, HasDerivAt P.A (P.A' x) x := by
      intro x hx
      have hx' : x ∈ Set.Icc a R := by simpa [Set.uIcc_of_le haR] using hx
      have hx1 : x ∈ Set.Ioi (1 : ℝ) := lt_of_lt_of_le ha1 hx'.1
      exact P.hA x hx1
    have hA'_on : ∀ x ∈ Set.uIcc a R, HasDerivAt P.A' (P.A'' x) x := by
      intro x hx
      have hx' : x ∈ Set.Icc a R := by simpa [Set.uIcc_of_le haR] using hx
      have hx1 : (1 : ℝ) < x := lt_of_lt_of_le ha1 hx'.1
      exact P.hA' x hx1
    -- Now apply the generalized skew identity.
    simpa using
      (NavierStokes.Radial.integral_radial_skew_identity_from
        (A := P.A) (A' := P.A') (A'' := P.A'') (a := a) (R := R)
        haR ha0 hA_on hA'_on hA'_int hV'_int)

  -- Expand `rm2uOp` and finish by linearity: skew part + potential `6/r^2 * A` part.
  -- Note: `(6/(r^2))*A * A * r^2 = 6 * A^2`.
  have hpot :
      (∫ x in a..R, ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)) =
        6 * ∫ x in a..R, (P.A x) ^ 2 := by
    -- First rewrite the integrand pointwise to `(6 : ℝ) * (A x)^2`.
    have hcongr :
        (∫ x in a..R, ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)) =
          ∫ x in a..R, (6 : ℝ) * (P.A x) ^ 2 := by
      refine (intervalIntegral.integral_congr (μ := volume)
        (f := fun x : ℝ => ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2))
        (g := fun x : ℝ => (6 : ℝ) * (P.A x) ^ 2) ?_)
      intro x hx
      -- On `[a,R]` we have `x ≠ 0` because `a > 0`.
      have ha0 : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1) ha1
      have hx' : x ∈ Set.Icc a R := by simpa [Set.uIcc_of_le haR] using hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hx'.1)
      field_simp [hx0]
      -- `field_simp` already reduces this to a trivial ring identity.
    -- Then pull the constant out of the interval integral.
    calc
      (∫ x in a..R, ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)) =
          ∫ x in a..R, (6 : ℝ) * (P.A x) ^ 2 := hcongr
      _ = (6 : ℝ) * ∫ x in a..R, (P.A x) ^ 2 := by
          simp

  -- Combine: rewrite the integrand pointwise as `f + g`, then apply linearity.
  let f : ℝ → ℝ := fun x : ℝ =>
    (-(P.A'' x) - (2 / x) * (P.A' x)) * (P.A x) * (x ^ 2)
  let g : ℝ → ℝ := fun x : ℝ =>
    ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)
  have hcongr :
      (∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)) =
        ∫ x in a..R, f x + g x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [rm2uOp, f, g, mul_add, mul_left_comm, mul_comm]
  have hadd :
      (∫ x in a..R, f x + g x) =
        (∫ x in a..R, f x) + ∫ x in a..R, g x := by
    -- `intervalIntegral.integral_add` needs the integrability hypotheses `hf` and `hg`.
    simpa [f, g] using
      (intervalIntegral.integral_add (μ := volume) (a := a) (b := R)
        (f := f) (g := g) hf hg)

  -- Rewrite using `hskew` and `hpot`.
  calc
    (∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)) = ∫ x in a..R, f x + g x := hcongr
    _ = (∫ x in a..R, f x) + ∫ x in a..R, g x := hadd
    _ =
        ((-(P.A R) * (R ^ 2 * P.A' R) + (P.A a) * (a ^ 2 * P.A' a))
          + ∫ x in a..R, (P.A' x) ^ 2 * (x ^ 2))
          + 6 * ∫ x in a..R, (P.A x) ^ 2 := by
          -- `hskew` rewrites `∫ f`, and `hpot` rewrites `∫ g`.
          simp [f, g, hskew, hpot, add_assoc]
    _ =
        (-(P.A R) * (R ^ 2 * P.A' R) + (P.A a) * (a ^ 2 * P.A' a))
          + (∫ x in a..R, (P.A' x) ^ 2 * (x ^ 2))
          + 6 * (∫ x in a..R, (P.A x) ^ 2) := by
          -- `a + b + c` is parsed as `(a + b) + c`.
          -- `simp` may cancel the common prefix on both sides, leaving a reflexive goal.
          simp [add_assoc]

/-- If the RM2U boundary term `(-A) * (A' * r^2)` and its derivative are integrable on `(1,∞)`,
then the tail flux vanishes at infinity.

This is exactly `SkewHarmGate.Radial.zeroSkewAtInfinity_of_integrable`, re-exported in the RM2U namespace.
-/
theorem tailFluxVanish_of_integrable
    (P : RM2URadialProfile)
    (hB_int :
      IntegrableOn (fun x : ℝ => (-P.A x) * ((P.A' x) * (x ^ 2))) (Set.Ioi (1 : ℝ)) volume)
    (hB'_int :
      IntegrableOn
        (fun x : ℝ =>
          (-(P.A' x)) * ((P.A' x) * (x ^ 2)) + (-P.A x) * ((P.A'' x) * (x ^ 2) + (P.A' x) * (2 * x)))
        (Set.Ioi (1 : ℝ)) volume) :
    TailFluxVanish P.A P.A' := by
  -- Delegate to the already formalized boundary-term lemma.
  simpa [TailFluxVanish, tailFlux] using
    (NavierStokes.Radial.zeroSkewAtInfinity_of_integrable
      (A := P.A) (A' := P.A') (A'' := P.A'')
      (hA := P.hA) (hA' := P.hA') hB_int hB'_int)

/-!
## Remaining “algebraic spine” interface

The manuscript’s RM2U block uses an energy identity for the \(\ell=2\) radial coefficient PDE:
once the **boundary term at infinity** vanishes, one obtains a coercive \(L^2\) estimate.

We do not yet encode the full PDE-in-time in Lean, but we *can* already state (and prove) the
time-slice “coercive estimate from tail-flux vanishing” provided we explicitly assume the
finite-window energy/forcing control needed to pass to the limit \(R\to\infty\).
-/

/-- **Energy/forcing hypothesis interface (explicit).**

This packages the precise extra assumptions needed to turn the *algebraic* identity
`integral_rm2uOp_mul_energy_identity` into the *global* coercive bound on `(1,∞)` once the
tail-flux vanishes.

In PDE terms, this is where (time-derivative + forcing) control would enter; in our time-slice
abstraction we expose it as a uniform bound on the interval integrals of the pairing
`(rm2uOp P) * (A) * r^2` on `[a,R]`.
-/
structure TailFluxVanishImpliesCoerciveHypothesisAt (P : RM2URadialProfile) (a : ℝ) : Prop where
  ha1 : 1 < a
  /-- Local integrability on the near-field window `(1,a]`. -/
  hA2_local : IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioc (1 : ℝ) a) volume
  hA'2_local : IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioc (1 : ℝ) a) volume
  /-- Interval-integrability assumptions to apply `integral_rm2uOp_mul_energy_identity` on `[a,R]`. -/
  hA'_int : ∀ R : ℝ, a ≤ R → IntervalIntegrable P.A' volume a R
  hV'_int :
    ∀ R : ℝ, a ≤ R →
      IntervalIntegrable (fun x : ℝ => (2 * x) * (P.A' x) + (x ^ 2) * (P.A'' x)) volume a R
  hf :
    ∀ R : ℝ, a ≤ R →
      IntervalIntegrable
        (fun x : ℝ => (-(P.A'' x) - (2 / x) * (P.A' x)) * (P.A x) * (x ^ 2)) volume a R
  hg :
    ∀ R : ℝ, a ≤ R →
      IntervalIntegrable
        (fun x : ℝ => ((6 / (x ^ 2)) * (P.A x)) * (P.A x) * (x ^ 2)) volume a R
  /-- Uniform bound on the energy/forcing pairing on `[a,R]`. -/
  hPairBound :
    ∃ C : ℝ,
      ∀ R : ℝ, a ≤ R →
        |∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)| ≤ C

/-- **Energy/forcing hypothesis interface (explicit).**

This is the existential wrapper over `TailFluxVanishImpliesCoerciveHypothesisAt`, so downstream
composition lemmas only need to pass around one hypothesis object.
-/
def TailFluxVanishImpliesCoerciveHypothesis (P : RM2URadialProfile) : Prop :=
  ∃ a : ℝ, TailFluxVanishImpliesCoerciveHypothesisAt P a

/-- **Theorem (time-slice coercive bound):**
under the explicit hypothesis interface above, `TailFluxVanish` implies `CoerciveL2Bound`.

This is the Lean-side replacement for the old black-box interface.
-/
theorem coerciveL2Bound_of_tailFluxVanish
    (P : RM2URadialProfile)
    (hTC : TailFluxVanishImpliesCoerciveHypothesis P)
    (hFlux : TailFluxVanish P.A P.A') :
    CoerciveL2Bound P := by
  classical
  -- Notation.
  rcases hTC with ⟨a, hTC⟩
  have ha1 : 1 < a := hTC.ha1

  -- A uniform bound on the pairing term.
  rcases hTC.hPairBound with ⟨C, hC⟩
  set Ca : ℝ := |(P.A a) * (a ^ 2 * P.A' a)|

  -- Tail-flux is eventually small (use radius `1` for concreteness).
  have hTailSmall : ∀ᶠ r in Filter.atTop, |tailFlux P.A P.A' r| ≤ (1 : ℝ) := by
    have hball : Metric.ball (0 : ℝ) (1 : ℝ) ∈ 𝓝 (0 : ℝ) := by
      simpa using (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    have h := hFlux.eventually hball
    filter_upwards [h] with r hr
    -- `hr : tailFlux ... r ∈ ball 0 1`
    have : |tailFlux P.A P.A' r| < (1 : ℝ) := by
      simpa [Metric.mem_ball, Real.dist_eq] using hr
    exact le_of_lt this

  -- We will apply the improper-integral criterion with `b n = (n : ℝ)`.
  let b : ℕ → ℝ := fun n => (n : ℝ)
  have hb : Filter.Tendsto b Filter.atTop Filter.atTop := by
    simpa [b] using (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

  have hEventually_ge_a : ∀ᶠ n in Filter.atTop, a ≤ b n := by
    exact hb.eventually (eventually_ge_atTop a)

  have hTailSmall_nat : ∀ᶠ n in Filter.atTop, |tailFlux P.A P.A' (b n)| ≤ (1 : ℝ) :=
    hb.eventually hTailSmall

  -- Helper: integrability on bounded windows `Ioc a (b n)` from differentiability (or empty if `b n ≤ a`).
  have hIntA2_window :
      ∀ n : ℕ, IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioc a (b n)) volume := by
    intro n
    by_cases hna : b n ≤ a
    · -- empty interval
      -- if `b n ≤ a`, then `(a, b n]` is empty
      simp [Set.Ioc_eq_empty_of_le hna]
    · -- nonempty interval: use continuity on `Icc a (b n)` (since `a>1`)
      have han : a ≤ b n := le_of_not_ge hna
      have hcontA : ContinuousOn P.A (Set.Icc a (b n)) := by
        intro x hx
        have hx1 : x ∈ Set.Ioi (1 : ℝ) := lt_of_lt_of_le ha1 hx.1
        exact (P.hA x hx1).continuousAt.continuousWithinAt
      have hcont : ContinuousOn (fun r : ℝ => (P.A r) ^ 2) (Set.Icc a (b n)) := by
        simpa [pow_two] using hcontA.mul hcontA
      have hint : IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Icc a (b n)) volume :=
        hcont.integrableOn_Icc
      exact hint.mono_set (by
        intro x hx
        exact ⟨le_of_lt hx.1, hx.2⟩)

  have hIntA'2_window :
      ∀ n : ℕ, IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioc a (b n)) volume := by
    intro n
    by_cases hna : b n ≤ a
    ·
      simp [Set.Ioc_eq_empty_of_le hna]
    ·
      have han : a ≤ b n := le_of_not_ge hna
      have hcontA' : ContinuousOn P.A' (Set.Icc a (b n)) := by
        intro x hx
        have hx1 : x ∈ Set.Ioi (1 : ℝ) := lt_of_lt_of_le ha1 hx.1
        exact (P.hA' x hx1).continuousAt.continuousWithinAt
      have hcont : ContinuousOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Icc a (b n)) := by
        -- product of continuous functions on a compact interval
        have h1 : ContinuousOn (fun r : ℝ => (P.A' r) ^ 2) (Set.Icc a (b n)) := by
          simpa [pow_two] using hcontA'.mul hcontA'
        have h2 : ContinuousOn (fun r : ℝ => r ^ 2) (Set.Icc a (b n)) := by
          exact (continuous_id.pow 2).continuousOn
        simpa [mul_assoc] using h1.mul h2
      have hint : IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Icc a (b n)) volume :=
        hcont.integrableOn_Icc
      exact hint.mono_set (by
        intro x hx
        exact ⟨le_of_lt hx.1, hx.2⟩)

  -- Key estimate on large windows: bounds the cumulative coercive cost on `[a, b n]`.
  have hCoerciveBound_nat :
      ∀ᶠ n in Filter.atTop,
        (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) + 6 * (∫ x in a..b n, (P.A x) ^ 2)
          ≤ C + (1 : ℝ) + Ca := by
    filter_upwards [hEventually_ge_a, hTailSmall_nat] with n han htail
    -- Apply the finite-window identity at `R = b n`.
    have hE :=
      integral_rm2uOp_mul_energy_identity (P := P) (a := a) (R := b n)
        (ha1 := ha1) (haR := han)
        (hA'_int := hTC.hA'_int (b n) han)
        (hV'_int := hTC.hV'_int (b n) han)
        (hf := hTC.hf (b n) han)
        (hg := hTC.hg (b n) han)
    -- Rewrite the boundary term at `R` in terms of `tailFlux`.
    have hBabs :
        |-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)|
          ≤ |tailFlux P.A P.A' (b n)| + Ca := by
      -- triangle inequality + rewrite the first term as `tailFlux`
      set x : ℝ := -(P.A (b n)) * ((b n) ^ 2 * P.A' (b n))
      set y : ℝ := (P.A a) * (a ^ 2 * P.A' a)
      have htri : |x + y| ≤ |x| + |y| := by
        simpa [Real.norm_eq_abs] using (norm_add_le x y)
      have hx : x = tailFlux P.A P.A' (b n) := by
        simp [x, tailFlux, mul_left_comm, mul_comm]
      have hy : |y| = Ca := by
        simp [y, Ca]
      -- rewrite `|x|` to `|tailFlux ...|` using `hx` (without unfolding `tailFlux` further)
      calc
        |-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)|
            = |x + y| := by simp [x, y]
        _ ≤ |x| + |y| := htri
        _ = |tailFlux P.A P.A' (b n)| + Ca := by simp [hx, hy]
    -- Bound the pairing term by `C`.
    have hpair : |∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2)| ≤ C :=
      hC (b n) han
    -- Now rearrange `hE` to isolate the coercive sum, then bound by abs-values.
    have hsum :
        (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) + 6 * (∫ x in a..b n, (P.A x) ^ 2) =
          (∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2))
            - (-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)) := by
      linarith [hE]
    -- Use `x - y ≤ |x| + |y|`.
    have hsub_le :
        (∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2))
            - (-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a))
          ≤ |∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2)|
            + |-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)| := by
      -- `x - y = x + (-y)` and each term is bounded by its absolute value.
      set x : ℝ := ∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2)
      set y : ℝ := (-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a))
      have h1 : x ≤ |x| := le_abs_self x
      have h2 : -y ≤ |y| := by
        simpa [abs_neg] using (le_abs_self (-y))
      -- add the inequalities and unfold `x,y`
      simpa [x, y, sub_eq_add_neg, add_assoc] using add_le_add h1 h2
    -- Put everything together.
    calc
      (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) + 6 * (∫ x in a..b n, (P.A x) ^ 2)
          = (∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2))
              - (-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)) := hsum
      _ ≤ |∫ x in a..b n, (rm2uOp P x) * (P.A x) * (x ^ 2)|
            + |-(P.A (b n)) * ((b n) ^ 2 * P.A' (b n)) + (P.A a) * (a ^ 2 * P.A' a)| := hsub_le
      _ ≤ C + (|tailFlux P.A P.A' (b n)| + Ca) := by
            gcongr
      _ ≤ C + ((1 : ℝ) + Ca) := by
            gcongr
      _ = C + (1 : ℝ) + Ca := by ring

  -- From the coercive-sum bound we get separate bounds for `A^2` and `(A')^2*r^2`.
  have hA2_bound :
      ∀ᶠ n in Filter.atTop, (∫ x in a..b n, (P.A x) ^ 2) ≤ (C + (1 : ℝ) + Ca) / 6 := by
    filter_upwards [hEventually_ge_a, hCoerciveBound_nat] with n han hsum
    have hnonneg :
        0 ≤ ∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2) := by
      refine intervalIntegral.integral_nonneg_of_forall (μ := volume) han ?_
      intro x
      exact mul_nonneg (sq_nonneg (P.A' x)) (sq_nonneg x)
    have hIA6 :
        6 * (∫ x in a..b n, (P.A x) ^ 2)
          ≤ C + (1 : ℝ) + Ca := by
      -- `6*IA ≤ IAprime + 6*IA ≤ bound`
      have : 6 * (∫ x in a..b n, (P.A x) ^ 2)
          ≤ (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) + 6 * (∫ x in a..b n, (P.A x) ^ 2) := by
        linarith
      exact le_trans this hsum
    -- divide by 6
    have hpos : (0 : ℝ) < 6 := by norm_num
    nlinarith

  have hA'2_bound :
      ∀ᶠ n in Filter.atTop, (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) ≤ C + (1 : ℝ) + Ca := by
    filter_upwards [hEventually_ge_a, hCoerciveBound_nat] with n han hsum
    have hnonneg :
        0 ≤ ∫ x in a..b n, (P.A x) ^ 2 := by
      exact intervalIntegral.integral_nonneg_of_forall (μ := volume) han (fun _ => sq_nonneg _)
    have : (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2))
          ≤ (∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2)) + 6 * (∫ x in a..b n, (P.A x) ^ 2) := by
      linarith
    exact le_trans this hsum

  -- Upgrade bounded interval-integrals to integrability on `(a,∞)`.
  have hA2_Ioi_a :
      IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioi a) volume := by
    refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (μ := volume) (l := Filter.atTop) (b := b) (I := (C + (1 : ℝ) + Ca) / 6) (a := a)
      (hfi := ?_) (hb := hb) (h := ?_)
    · intro n
      -- `Ioc a (b n) ⊆ Ioc a (b n)`; use the window lemma
      simpa [MeasureTheory.IntegrableOn] using (hIntA2_window n)
    · -- bound on the norm interval integral (eventually)
      filter_upwards [hEventually_ge_a, hA2_bound] with n han hbd
      -- `‖(A^2)‖ = A^2` pointwise
      have hnorm :
          (∫ x in a..b n, ‖(P.A x) ^ 2‖ ∂volume) = ∫ x in a..b n, (P.A x) ^ 2 := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        simp [Real.norm_eq_abs]
      simpa [hnorm] using hbd

  have hA'2_Ioi_a :
      IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioi a) volume := by
    refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (μ := volume) (l := Filter.atTop) (b := b) (I := (C + (1 : ℝ) + Ca)) (a := a)
      (hfi := ?_) (hb := hb) (h := ?_)
    · intro n
      simpa [MeasureTheory.IntegrableOn] using (hIntA'2_window n)
    · filter_upwards [hEventually_ge_a, hA'2_bound] with n han hbd
      have hnorm :
          (∫ x in a..b n, ‖(P.A' x) ^ 2 * (x ^ 2)‖ ∂volume) =
            ∫ x in a..b n, (P.A' x) ^ 2 * (x ^ 2) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        simp [Real.norm_eq_abs]
      simpa [hnorm] using hbd

  -- Combine near-field `(1,a]` with tail `(a,∞)` to get integrability on `(1,∞)`.
  have hA2_Ioi1 :
      IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioi (1 : ℝ)) volume := by
    have hunion : Set.Ioc (1 : ℝ) a ∪ Set.Ioi a = Set.Ioi (1 : ℝ) := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx.1
        · exact lt_trans ha1 hx
      · intro hx
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hx, hxa⟩
        · exact Or.inr (lt_of_not_ge hxa)
    -- use `IntegrableOn.union`
    have := (hTC.hA2_local.union hA2_Ioi_a)
    simpa [hunion] using this

  have hA'2_Ioi1 :
      IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioi (1 : ℝ)) volume := by
    have hunion : Set.Ioc (1 : ℝ) a ∪ Set.Ioi a = Set.Ioi (1 : ℝ) := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx.1
        · exact lt_trans ha1 hx
      · intro hx
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hx, hxa⟩
        · exact Or.inr (lt_of_not_ge hxa)
    have := (hTC.hA'2_local.union hA'2_Ioi_a)
    simpa [hunion] using this

  exact ⟨hA2_Ioi1, hA'2_Ioi1⟩

end RM2U
end NavierStokes
-- end IndisputableMonolith
