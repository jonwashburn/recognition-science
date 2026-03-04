/-!
# Recognition Science — Lean 4 Formalization

A zero-parameter derivation of fundamental physics from a single functional
equation (the Recognition Composition Law) and the combinatorics of the
3-cube Q₃.

## Module Structure

### Cost — The unique cost functional J(x)
- `RecognitionScience.Cost`: J(x) = ½(x + x⁻¹) − 1, properties
- `RecognitionScience.Cost.FunctionalEquation`: RCL → d'Alembert → J uniqueness

### Constants — Fundamental constants from φ and D=3
- `RecognitionScience.Constants`: φ, ℏ = φ⁻⁵, G, κ = 8φ⁵
- `RecognitionScience.Constants.AlphaDerivation`: α⁻¹ from cube geometry

### Foundation — Structural theorems T0–T8
- `RecognitionScience.Foundation.LogicFromCost`: T0 — Logic from cost
- `RecognitionScience.Foundation.PhiForcing`: T6 — φ from self-similarity
- `RecognitionScience.Foundation.EightTick`: T7 — 8-tick period
- `RecognitionScience.Foundation.DimensionForcing`: T8 — D = 3

### Masses — The fermion mass spectrum
- `RecognitionScience.Masses.MassLaw`: Master mass law
- `RecognitionScience.Masses.BaselineDerivation`: Baseline rungs from cube geometry
- `RecognitionScience.Masses.GapFunctionForcing`: Gap function uniqueness

### Gravity — Emergent gravity from J-cost
- `RecognitionScience.Gravity.ZeroParameterGravity`: κ = 8φ⁵, equivalence principle
- `RecognitionScience.Gravity.NoGraviton`: Gravity is emergent, not force-mediated

### Unification — The complete forcing chain
- `RecognitionScience.Unification.RSMasterTheorem`: T0–T8 master theorem
- `RecognitionScience.Unification.AllConstantsFromPhi`: All constants from φ
-/

import RecognitionScience.Constants
import RecognitionScience.Cost
import RecognitionScience.Foundation.EightTick
import RecognitionScience.Foundation.PhiForcing
import RecognitionScience.Foundation.DimensionForcing
import RecognitionScience.Masses.MassLaw
import RecognitionScience.Masses.BaselineDerivation
import RecognitionScience.Gravity.ZeroParameterGravity
