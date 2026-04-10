import NavierStokes.RM2U.Core

/-!
# RM2U.RM2Closure (interface layer)

This file is meant to host the fully classical “coercive \(\ell=2\) ⇒ RM2” closure steps
from `navier-dec-12-rewrite.tex`, namely:

- coercive \(\ell=2\) control ⇒ finiteness of the log-critical shell moment `∫ |A|/r`,
- finiteness of that shell moment ⇒ boundedness of the affine/harmonic obstruction (RM2).

For now, we keep the final “RM2 statement” abstract and provide a single *interface* hypothesis
to prevent scattering assumptions across the codebase. The plan is to later replace this
hypothesis with explicit proofs mirroring the TeX.
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes
namespace RM2U

open MeasureTheory Set

/-- Placeholder definition of “RM2 is closed” for a time-slice coefficient.

In the manuscript, RM2 is equivalent to boundedness of the log-critical \(\ell=2\) tail moment.
We encode that equivalence in the simplest Lean-friendly way:

`RM2Closed A := LogCriticalMomentFinite A`.

Later we can refine this to match a more explicit fixed-frame compactness statement. -/
def RM2Closed (A : ℝ → ℝ) : Prop :=
  LogCriticalMomentFinite A

/-- **Coercive \(\ell=2\) control ⇒ log-critical moment finiteness (RM2 in this simplified model).**

This is the Lean translation of the manuscript’s one-line Cauchy–Schwarz argument:

If `A ∈ L²((1,∞),dr)`, then `A/r ∈ L¹((1,∞),dr)` since `1/r ∈ L²((1,∞),dr)`.

We package it in a way that is robust to later refactors of what “RM2 closed” means:
at minimum, coercive control implies the log-critical shell moment is absolutely convergent.
-/
theorem rm2Closed_of_coerciveL2Bound (P : RM2URadialProfile) :
    CoerciveL2Bound P → RM2Closed P.A := by
  intro hco
  -- Unpack the L² control of `A`.
  have hA2 : IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioi (1 : ℝ)) volume :=
    hco.1

  -- We will dominate `‖A(r)/r‖` by `A(r)^2 + r^(-2)` on `r > 1`.
  -- First, record integrability of `r ^ (-2)` (real power) on `(1,∞)`.
  have hRpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume := by
    -- `(-2) < -1`, so the real power is integrable at infinity.
    have hlt : (-2 : ℝ) < -1 := by linarith
    simpa using (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ)) hlt zero_lt_one)

  have hdom : IntegrableOn (fun r : ℝ => (P.A r) ^ 2 + r ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume :=
    hA2.add hRpow

  -- `A/r` is continuous on `(1,∞)` (hence ae-strongly measurable on that set),
  -- because `HasDerivAt` implies continuity pointwise.
  have hcontA : ContinuousOn P.A (Set.Ioi (1 : ℝ)) := by
    intro x hx
    exact (P.hA x hx).continuousAt.continuousWithinAt

  have hcontInv : ContinuousOn (fun r : ℝ => r⁻¹) (Set.Ioi (1 : ℝ)) := by
    -- `inv` is continuous away from `0`; `(1,∞) ⊆ {0}ᶜ`.
    refine (continuousOn_inv₀ : ContinuousOn (Inv.inv : ℝ → ℝ) ({0}ᶜ)).mono ?_
    intro r hr
    have : (r : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (mem_Ioi.1 hr))
    simpa [Set.mem_compl_singleton_iff] using this

  have hcontDiv : ContinuousOn (fun r : ℝ => P.A r / r) (Set.Ioi (1 : ℝ)) := by
    -- `A/r = A * r⁻¹`.
    simpa [div_eq_mul_inv] using hcontA.mul hcontInv

  have hf_meas : AEStronglyMeasurable (fun r : ℝ => P.A r / r)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact hcontDiv.aestronglyMeasurable measurableSet_Ioi

  -- Pointwise domination on `(1,∞)`:
  -- `‖A/r‖ = |A| * r^(-1) ≤ |A|^2 + (r^(-1))^2 = A^2 + r^(-2)`.
  have h_le :
      ∀ᵐ r : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))),
        ‖P.A r / r‖ ≤ (P.A r) ^ 2 + r ^ (-2 : ℝ) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro r hr
    have hr0 : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) (mem_Ioi.1 hr).le
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1) (mem_Ioi.1 hr)
    -- Rewrite norms as abs; keep `|A| / r` form for easier final `simp`.
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos hrpos]
    -- Reduce to an AM-GM style inequality.
    -- Let a = |A r|, b = r^(-1).
    have ha : 0 ≤ |P.A r| := abs_nonneg (P.A r)
    have hb : 0 ≤ r ^ (-1 : ℝ) := by
      -- real power of a nonnegative base is nonnegative
      exact Real.rpow_nonneg hr0 (-1 : ℝ)
    -- `|A| * r^(-1) ≤ |A|^2 + (r^(-1))^2` using `two_mul_le_add_sq` and `ab ≤ 2ab`.
    have hab0 : 0 ≤ |P.A r| * (r ^ (-1 : ℝ)) := mul_nonneg ha hb
    have h2 : 2 * |P.A r| * (r ^ (-1 : ℝ)) ≤ |P.A r| ^ 2 + (r ^ (-1 : ℝ)) ^ 2 :=
      two_mul_le_add_sq (|P.A r|) (r ^ (-1 : ℝ))
    have h1 : |P.A r| * (r ^ (-1 : ℝ)) ≤ 2 * |P.A r| * (r ^ (-1 : ℝ)) := by
      -- since `0 ≤ ab`, we have `ab ≤ 2ab`
      nlinarith
    have hmain : |P.A r| * (r ^ (-1 : ℝ)) ≤ |P.A r| ^ 2 + (r ^ (-1 : ℝ)) ^ 2 :=
      le_trans h1 h2
    -- Rewrite `(r^(-1))^2` as `r^(-2)` and `|A|^2` as `A^2`.
    have hrpow2 : (r ^ (-1 : ℝ)) ^ 2 = r ^ (-2 : ℝ) := by
      -- `r^(-2) = (r^(-1))^2` for `r ≥ 0`
      have : r ^ ((-1 : ℝ) * (2 : ℝ)) = (r ^ (-1 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_mul (x := r) hr0 (-1 : ℝ) (2 : ℝ))
      -- convert real exponent `2` to nat power `2`
      simpa [show (-1 : ℝ) * (2 : ℝ) = (-2 : ℝ) by ring, Real.rpow_two] using this.symm
    -- Convert `|A| / r` to `|A| * r⁻¹` and compare `r⁻¹` with `r ^ (-1)`.
    have hdiv : |P.A r| / r = |P.A r| * r⁻¹ := by
      simp [div_eq_mul_inv]

    -- On `r > 0`, `r ^ (-1 : ℝ) = r⁻¹`.
    have hrpow1 : r ^ (-1 : ℝ) = r⁻¹ := by
      simpa using (Real.rpow_neg_one r)

    -- Finish: rewrite everything into the target shape.
    -- `|A|^2 = A^2` in ℝ, and `(r⁻¹)^2 = (r^2)⁻¹`.
    -- Also use `hrpow2` to replace `(r^(-1))^2` by `r^(-2)`.
    -- We keep the RHS as `A^2 + r^(-2)` to match the outer goal.
    have : |P.A r| / r ≤ (P.A r) ^ 2 + r ^ (-2 : ℝ) := by
      -- start from the inequality on `|A| * r^(-1)`
      have hmain' :
          |P.A r| * r⁻¹ ≤ |P.A r| ^ 2 + (r⁻¹) ^ 2 := by
        -- replace `r^(-1)` with `r⁻¹` in `hmain`
        simpa [hrpow1] using hmain
      -- rewrite the RHS and LHS into the requested form
      -- `(r⁻¹)^2 = (r^2)⁻¹`, and `(P.A r)^2 = |P.A r|^2`.
      -- Then replace `(r⁻¹)^2` by `r^(-2)` via `hrpow2`.
      -- Finally convert `|A|*r⁻¹` to `|A|/r`.
      -- Note: `hrpow2` is about `r^(-1)` not `r⁻¹`; use `hrpow1` to bridge.
      have hrpow2' : (r⁻¹) ^ 2 = r ^ (-2 : ℝ) := by
        -- `(r⁻¹)^2 = (r^(-1))^2 = r^(-2)`
        simpa [hrpow1] using hrpow2
      -- and `|A|^2 = A^2`
      have habs2 : |P.A r| ^ 2 = (P.A r) ^ 2 := by
        simp [pow_two]
      -- assemble
      calc
        |P.A r| / r = |P.A r| * r⁻¹ := hdiv
        _ ≤ |P.A r| ^ 2 + (r⁻¹) ^ 2 := hmain'
        _ = (P.A r) ^ 2 + r ^ (-2 : ℝ) := by
              simp [habs2, hrpow2']
    exact this

  -- Conclude integrability by domination.
  -- We use the `Integrable.mono'` lemma on the restricted measure.
  have : Integrable (fun r : ℝ => P.A r / r) (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    (hdom.integrable).mono' hf_meas h_le

  -- Repackage as `IntegrableOn` and match `RM2Closed`.
  simpa [RM2Closed, LogCriticalMomentFinite, IntegrableOn] using this

/-- Interface hypothesis: coercive \(\ell=2\) control implies RM2 closure for this profile.

This is *not* intended to remain an assumption long-term; it is a single placeholder
so that downstream developments can depend on one named lemma instead of ad hoc assumptions. -/
structure CoerciveImpliesRM2Hypothesis (P : RM2URadialProfile) : Prop where
  implies : CoerciveL2Bound P → RM2Closed P.A

namespace CoerciveImpliesRM2Hypothesis

/-- Construct the (now purely formal) interface hypothesis from the proved lemma
`rm2Closed_of_coerciveL2Bound`. This is here for backwards compatibility: downstream code can
depend on a named hypothesis while the file still remains `sorry`/`axiom` free. -/
theorem of_proved (P : RM2URadialProfile) : CoerciveImpliesRM2Hypothesis P :=
  ⟨rm2Closed_of_coerciveL2Bound (P := P)⟩

end CoerciveImpliesRM2Hypothesis

end RM2U
end NavierStokes
-- end IndisputableMonolith
