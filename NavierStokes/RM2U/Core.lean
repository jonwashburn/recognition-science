import Mathlib

/-!
# RM2U.Core (spec layer)

This module is the Lean-side **spec** for the RM2U “tail/tightness” gate in
`navier-dec-12-rewrite.tex`, refactored into a 1D radial coefficient problem.

Key idea:
- Fix a time `t` and a spherical direction/test field parameter `b`.
- Work with the resulting scalar radial coefficient `A(r)` for `r ≥ 1`.
- The RM2U obstruction can be expressed through a **boundary / tail-flux term**
  `(-A(r)) * (A'(r) * r^2)` as `r → ∞`.

All analytic identities are proved in `RM2U.EnergyIdentity` by reusing
`NavierStokes.SkewHarmGate`.
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes
namespace RM2U

open scoped Topology Interval
open Filter MeasureTheory Set

/-- Boundary term / tail-flux term appearing in the radial integration-by-parts identity:

`B(r) := (-A(r)) * (A'(r) * r^2)`.

This matches `SkewHarmGate.Radial.zeroSkewAtInfinity_of_integrable`.
-/
noncomputable def tailFlux (A A' : ℝ → ℝ) (r : ℝ) : ℝ :=
  (-A r) * ((A' r) * (r ^ 2))

/-- “Tail flux vanishes at infinity”: the boundary term tends to `0` as `r → ∞`. -/
def TailFluxVanish (A A' : ℝ → ℝ) : Prop :=
  Tendsto (fun r : ℝ => tailFlux A A' r) atTop (𝓝 0)

/-- Abstract profile for a fixed time-slice RM2U coefficient, with derivative data. -/
structure RM2URadialProfile where
  A : ℝ → ℝ
  A' : ℝ → ℝ
  A'' : ℝ → ℝ
  hA : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A (A' x) x
  hA' : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt A' (A'' x) x

namespace RM2URadialProfile

/-- The boundary term associated to a profile. -/
noncomputable def boundaryTerm (P : RM2URadialProfile) : ℝ → ℝ :=
  fun r => tailFlux P.A P.A' r

/-- Convenience: `TailFluxVanish` for a profile. -/
def tailFluxVanish (P : RM2URadialProfile) : Prop :=
  TailFluxVanish P.A P.A'

end RM2URadialProfile

/-- A concrete analytic target implied by UEWE and used to close RM2U in the manuscript:
integrability of the \(\ell=2\) coefficient and its derivative with the `r^2` weight. -/
def CoerciveL2Bound (P : RM2URadialProfile) : Prop :=
  IntegrableOn (fun r : ℝ => (P.A r) ^ 2) (Set.Ioi (1 : ℝ)) volume
    ∧ IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioi (1 : ℝ)) volume

/-- The log-critical shell moment integrability (the RM2 obstruction in the manuscript):
`A(r)/r ∈ L¹((1,∞), dr)`. -/
def LogCriticalMomentFinite (A : ℝ → ℝ) : Prop :=
  IntegrableOn (fun r : ℝ => A r / r) (Set.Ioi (1 : ℝ)) volume

end RM2U
end NavierStokes
-- end IndisputableMonolith
