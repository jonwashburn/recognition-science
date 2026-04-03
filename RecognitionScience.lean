import RecognitionScience.Constants
import RecognitionScience.Cost
import RecognitionScience.Foundation.EightTick
import RecognitionScience.Foundation.PhiForcing
import RecognitionScience.Foundation.LedgerCanonicality
import RecognitionScience.Foundation.HierarchyMinimality
import RecognitionScience.Foundation.HierarchyEmergence
import RecognitionScience.Foundation.HierarchyForcing
import RecognitionScience.Foundation.HierarchyDynamics
import RecognitionScience.Foundation.DimensionForcing
import RecognitionScience.Foundation.VariationalDynamics
import RecognitionScience.Foundation.MeasurementMechanism
import RecognitionScience.Foundation.Entanglement
import RecognitionScience.Foundation.GaugeFromCube
import RecognitionScience.Foundation.Thermodynamics
import RecognitionScience.Foundation.WindingCharges
import RecognitionScience.Foundation.ContinuumLimit
import RecognitionScience.Foundation.LinkingNumbers
import RecognitionScience.Masses.MassLaw
import RecognitionScience.Masses.BaselineDerivation
import RecognitionScience.Gravity.ZeroParameterGravity
import RecognitionScience.Foundation.DimensionalConstraints.Core
import RecognitionScience.Verification.DimensionalConstraintsCert
import RecognitionScience.Verification.Exclusivity.Framework
import RecognitionScience.Verification.Exclusivity.ModelIndependent
import RecognitionScience.Verification.Exclusivity.HierarchyTheorem
import RecognitionScience.Verification.Exclusivity.DimensionlessForcing
import RecognitionScience.Verification.Exclusivity.GroundStateRestriction
import RecognitionScience.Verification.Exclusivity.ObservableTypeEquiv
import RecognitionScience.Verification.Exclusivity.RCLDerivation
import RecognitionScience.Verification.Exclusivity.PredictionMap
import RecognitionScience.Verification.Exclusivity.ModelIndependentCert

/-!
# Recognition Science — Lean 4 Formalization

A zero-parameter derivation of fundamental physics from a single functional
equation (the Recognition Composition Law) and the combinatorics of the
3-cube Q₃.

This is the canonical namespace for the artifact analyzed in the submitted
JAR paper (Simons & Washburn, 2026), *Certificate-Based Verification of
Derivation-Graph Structural Properties in Lean 4/Mathlib*. The
`IndisputableMonolith` library provides internal support for structural
certification and observable-payload types.

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
- `RecognitionScience.Foundation.LedgerCanonicality`: zero-parameter comparison ledger interface
- `RecognitionScience.Foundation.HierarchyMinimality`: minimal hierarchy closure
- `RecognitionScience.Foundation.HierarchyEmergence`: uniform hierarchy emergence of φ
- `RecognitionScience.Foundation.HierarchyForcing`: zero-parameter forcing of additive hierarchy
- `RecognitionScience.Foundation.HierarchyDynamics`: T5→T6 bridge from ledger locality/minimality
- `RecognitionScience.Foundation.EightTick`: T7 — 8-tick period
- `RecognitionScience.Foundation.DimensionForcing`: T8 — D = 3
- `RecognitionScience.Foundation.VariationalDynamics`: F-008 — Ledger update rule
- `RecognitionScience.Foundation.MeasurementMechanism`: F-009 — Measurement mechanism
- `RecognitionScience.Foundation.Entanglement`: F-010 — Entanglement from RCL
- `RecognitionScience.Foundation.GaugeFromCube`: P-014 — SM gauge group from Q₃
- `RecognitionScience.Foundation.Thermodynamics`: F-011 — Temperature and thermodynamics
- `RecognitionScience.Foundation.WindingCharges`: F-013 — Topological charges from winding numbers
- `RecognitionScience.Foundation.ContinuumLimit`: F-014 — Continuum limit from J-cost
- `RecognitionScience.Foundation.LinkingNumbers`: F-015 — Linking numbers and conservation

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
