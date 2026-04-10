import NavierStokes.RM2U.EnergyIdentity

/-!
# RM2U.ProjectedPDE (hypothesis interface layer)

This file does **not** formalize the 3D Navier–Stokes projection yet. Instead it introduces a
Lean-facing *hypothesis interface* that matches the TeX lemma `lem:Ab-evolution`:

> `(∂_t - Δ_r + 6/r^2) A = F`

rewritten in our time-slice operator language as

> `rm2uOp(P) = F - A_t`

The point of this layer is purely *plumbing*: it turns separate bounds on the forcing pairing
and on the time-derivative pairing into the single “pairing bound” field required by
`TailFluxVanishImpliesCoerciveHypothesisAt`, which then unlocks the already-proved theorem
`coerciveL2Bound_of_tailFluxVanish`.
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes
namespace RM2U

open Filter MeasureTheory Set
open scoped Topology Interval

/-!
## Projected PDE hypothesis interface

Important Lean detail: `Prop`-valued structures cannot store data fields like functions.
So we parameterize the time-derivative/forcing functions explicitly.
-/

/-- Hypothesis: the RM2U operator pairing can be bounded by splitting `rm2uOp = F - A_t`.

This is intentionally *time-slice* and abstract: it doesn't define what `A_t`/`F` are, only that
they exist and can be paired against `A r^2` on `[a,R]`.
-/
structure ProjectedPDEPairingHypothesisAt (P : RM2URadialProfile) (a : ℝ)
    (At F : ℝ → ℝ) : Prop where
  /-- Pointwise relation on `(1,∞)`: `rm2uOp = F - At`. -/
  hDecomp : ∀ r ∈ Set.Ioi (1 : ℝ), rm2uOp P r = F r - At r
  /-- Interval-integrability of the forcing pairing on `[a,R]` (needed for linearity). -/
  hForceInt :
    ∀ R : ℝ, a ≤ R → IntervalIntegrable (fun x : ℝ => (F x) * (P.A x) * (x ^ 2)) volume a R
  /-- Interval-integrability of the time-derivative pairing on `[a,R]` (needed for linearity). -/
  hTimeInt :
    ∀ R : ℝ, a ≤ R → IntervalIntegrable (fun x : ℝ => (At x) * (P.A x) * (x ^ 2)) volume a R
  /-- Uniform bound on the forcing pairing on `[a,R]`. -/
  hForcePair :
    ∃ CF : ℝ, ∀ R : ℝ, a ≤ R → |∫ x in a..R, (F x) * (P.A x) * (x ^ 2)| ≤ CF
  /-- Uniform bound on the time-derivative pairing on `[a,R]`. -/
  hTimePair :
    ∃ CT : ℝ, ∀ R : ℝ, a ≤ R → |∫ x in a..R, (At x) * (P.A x) * (x ^ 2)| ≤ CT

/-- Build the `TailFluxVanishImpliesCoerciveHypothesisAt` interface from a projected PDE pairing
decomposition plus the remaining local/interval hypotheses.

This isolates the *single* extra analytic step that the TeX manuscript is implicitly using:
bounding `∫ (F - A_t) A r^2` by bounding the two pairings separately.
-/
theorem TailFluxVanishImpliesCoerciveHypothesisAt.of_projectedPDEPairing
    (P : RM2URadialProfile) (a : ℝ)
    (hbase : TailFluxVanishImpliesCoerciveHypothesisAt P a)
    {At F : ℝ → ℝ} (hpde : ProjectedPDEPairingHypothesisAt P a At F) :
    TailFluxVanishImpliesCoerciveHypothesisAt P a := by
  classical
  refine
    { ha1 := hbase.ha1
      hA2_local := hbase.hA2_local
      hA'2_local := hbase.hA'2_local
      hA'_int := hbase.hA'_int
      hV'_int := hbase.hV'_int
      hf := hbase.hf
      hg := hbase.hg
      hPairBound := ?_ }

  rcases hpde.hForcePair with ⟨CF, hCF⟩
  rcases hpde.hTimePair with ⟨CT, hCT⟩
  refine ⟨CF + CT, ?_⟩
  intro R haR

  -- Rewrite `rm2uOp` to `F - At` on `[a,R]` (note: `[a,R] ⊆ (1,∞)` because `1 < a`).
  have hcongr :
      (∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)) =
        ∫ x in a..R, ((F x) - (At x)) * (P.A x) * (x ^ 2) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc a R := by
      simpa [Set.uIcc_of_le haR] using hx
    have hx1 : x ∈ Set.Ioi (1 : ℝ) := lt_of_lt_of_le hbase.ha1 hx'.1
    simp [hpde.hDecomp x hx1]

  -- Triangle inequality: split the pairing into force and time-derivative parts.
  have hsplit :
      |∫ x in a..R, ((F x) - (At x)) * (P.A x) * (x ^ 2)|
        ≤ |∫ x in a..R, (F x) * (P.A x) * (x ^ 2)|
          + |∫ x in a..R, (At x) * (P.A x) * (x ^ 2)| := by
    -- `∫ ((F-At)*A*r^2) = ∫ (F*A*r^2) - ∫ (At*A*r^2)`.
    have hsub :
        (∫ x in a..R, ((F x) - (At x)) * (P.A x) * (x ^ 2)) =
          (∫ x in a..R, (F x) * (P.A x) * (x ^ 2))
            - ∫ x in a..R, (At x) * (P.A x) * (x ^ 2) := by
      -- pointwise: `(F-At)*A*r^2 = (F*A*r^2) - (At*A*r^2)`
      have hpt :
          (fun x : ℝ => ((F x) - (At x)) * (P.A x) * (x ^ 2)) =
            fun x : ℝ => (F x) * (P.A x) * (x ^ 2) - (At x) * (P.A x) * (x ^ 2) := by
        funext x
        ring
      -- linearity requires interval integrability
      simpa [hpt] using
        (intervalIntegral.integral_sub (μ := volume) (a := a) (b := R)
          (hf := hpde.hForceInt R haR) (hg := hpde.hTimeInt R haR))

    -- `|u - v| = |u + (-v)| ≤ |u| + |v|`
    set u : ℝ := ∫ x in a..R, (F x) * (P.A x) * (x ^ 2)
    set v : ℝ := ∫ x in a..R, (At x) * (P.A x) * (x ^ 2)
    have : |u - v| ≤ |u| + |v| := by
      -- triangle inequality in `ℝ` written via the norm
      simpa [Real.norm_eq_abs, sub_eq_add_neg, u, v] using (norm_add_le u (-v))
    simpa [hsub, u, v] using this

  calc
    |∫ x in a..R, (rm2uOp P x) * (P.A x) * (x ^ 2)|
        = |∫ x in a..R, ((F x) - (At x)) * (P.A x) * (x ^ 2)| := by
            simp [hcongr]
    _ ≤ |∫ x in a..R, (F x) * (P.A x) * (x ^ 2)|
          + |∫ x in a..R, (At x) * (P.A x) * (x ^ 2)| := hsplit
    _ ≤ CF + CT := by
          exact add_le_add (hCF R haR) (hCT R haR)

end RM2U
end NavierStokes
-- end IndisputableMonolith
