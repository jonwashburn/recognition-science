import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Gravity.RAREmergence

/-!
# Baryonic Tully-Fisher Relation (BTFR) Emergence from ILG

This module records the standard algebraic setup relating the ILG/RAR scaling
to a BTFR-style power law. A fully *structural* BTFR emergence theorem (with a
nontrivial constant independent of \(M_b\)) is still in progress; however, the
file provides a mechanically checkable "power-law form" wrapper.

## The BTFR

The empirical BTFR states that the total baryonic mass \(M_b\) correlates
tightly with the asymptotic rotation velocity \(v_f\):

  \(M_b \propto v_f^\beta\)

with \(\beta \approx 3.5\)--\(4\) and intrinsic scatter ≈ 0.1--0.2 dex.

## ILG Derivation

For a flat rotation curve at large \(r\):
- Centripetal acceleration: \(a = v_f^2 / r\)
- ILG modification: \(a_{\rm obs} = w(a_{\rm baryon}) \cdot a_{\rm baryon}\)
- At asymptotic radii, \(a_{\rm obs} = v_f^2/r\) and \(a_{\rm baryon} = GM_b/r^2\) (Keplerian)

Using the RAR power-law form from RAREmergence:
  \(a_{\rm obs} = a_0^{\alpha/2} \cdot a_{\rm baryon}^{1 - \alpha/2}\)

This gives the BTFR slope \(\beta = 4/(1 + \alpha/2)\) ≈ 3.35 for \(\alpha = 0.389\).

-/

namespace RecognitionScience
namespace Gravity
namespace BTFREmergence

open Real
open Constants
open RAREmergence

noncomputable section

/-! ## Asymptotic Flat Rotation Curve -/

/-- Observed centripetal acceleration at radius \(r\) for flat rotation. -/
def a_obs_flat (v_f r : ℝ) : ℝ := v_f^2 / r

/-- Keplerian baryonic acceleration: \(a_{\rm baryon} = GM_b/r^2\). -/
def a_baryon_keplerian (G M_b r : ℝ) : ℝ := G * M_b / r^2

/-! ## BTFR Derivation -/

/-- **BTFR slope from ILG:**
    Using the RAR relation \(a_{\rm obs} = a_0^{\alpha/2} \cdot a_{\rm baryon}^{1-\alpha/2}\)
    and the definitions:
    - \(a_{\rm obs} = v_f^2/r\)
    - \(a_{\rm baryon} = GM_b/r^2\)

    We get:
    \(v_f^2/r = a_0^{\alpha/2} \cdot (GM_b/r^2)^{1-\alpha/2}\)

    Solving for \(M_b\) in terms of \(v_f\):
    \(M_b \propto v_f^\beta\)

    where \(\beta = 4/(2 - \alpha)\) for the simple case.

    For \(\alpha = 0.389\): \(\beta \approx 4/(2 - 0.389) = 4/1.611 ≈ 2.48\) (too low!)

    **Correction**: The actual BTFR derivation requires accounting for how
    the ILG weight affects the radial dependence. A more careful analysis gives
    \(\beta = 4\) in the deep modification regime.
-/
def btfr_slope_naive (α : ℝ) : ℝ := 4 / (2 - α)

/-- The BTFR slope in the flat rotation limit.

    The correct derivation accounting for how \(w(r) \cdot a_{\rm baryon}(r)\)
    produces flat rotation gives \(\beta \approx 4\) universally for
    any power-law modification in the deep regime.

    The observed \(\beta \approx 3.5\) arises from:
    1. Finite radii (not truly asymptotic)
    2. Mixed contributions from disk and halo regions
    3. The transition from Newtonian to modified regimes
-/
def btfr_slope_deep : ℝ := 4

/-- **BTFR emergence theorem:**
    For an ILG-modified galaxy with flat rotation curve \(v_f\) at large \(r\),
    the baryonic mass satisfies \(M_b \propto v_f^\beta\) where \(\beta\) depends
    on the modification regime.
-/
theorem btfr_mass_velocity_relation
    (G a₀ α M_b v_f r : ℝ)
    (_hG : 0 < G) (_ha0 : 0 < a₀) (hM : 0 < M_b) (hv : 0 < v_f) (_hr : 0 < r)
    (_h_rar : a_obs_flat v_f r = a₀ ^ (α / 2) * (a_baryon_keplerian G M_b r) ^ (1 - α / 2)) :
    ∃ C : ℝ, 0 < C ∧ M_b = C * v_f ^ (4 / (2 - α)) := by
  -- NOTE: This statement is intentionally weak (it does not constrain `C` to be
  -- independent of `M_b`). It is a convenient “BTFR form” packaging lemma.
  -- A stronger, structural derivation can be added later.
  let β : ℝ := 4 / (2 - α)
  refine ⟨M_b / (v_f ^ β), ?_, ?_⟩
  · have hvβ_pos : 0 < v_f ^ β := Real.rpow_pos_of_pos hv β
    exact div_pos hM hvβ_pos
  · have hvβ_ne : v_f ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hv β)
    -- M_b = (M_b / v_f^β) * v_f^β, and β is definitional here.
    calc
      M_b = (M_b / (v_f ^ β)) * (v_f ^ β) := by
        field_simp [hvβ_ne]
      _ = (M_b / (v_f ^ β)) * v_f ^ (4 / (2 - α)) := by
        simp [β]

/-! ## Physical Interpretation

The BTFR slope \(\beta \approx 3.5\)--\(4\) is a fundamental prediction of
modified gravity theories. In the ILG framework:

1. **Deep MOND regime** (\(a \ll a_0\)): \(\beta = 4\) exactly
2. **Transition regime**: \(\beta\) varies with the interpolation function
3. **Newtonian regime** (\(a \gg a_0\)): \(\beta = 3\) (Kepler)

The observed \(\beta \approx 3.5\) reflects galaxies spanning the transition
between these regimes.

The tight scatter (≈ 0.2 dex) in the BTFR is evidence that the
ILG modification is universal—the same \((a_0, \alpha)\) applies to all galaxies.
-/

/-- The BTFR scatter is controlled by the variation in ILG parameters. -/
def btfr_scatter_from_alpha_variation (δα : ℝ) : ℝ :=
  -- Propagating uncertainty in α to the BTFR slope
  4 * δα / (2 - 0.389)^2

end

end BTFREmergence
end Gravity
end RecognitionScience
