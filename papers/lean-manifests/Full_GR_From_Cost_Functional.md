# Lean Closure Manifest: Full GR From Cost Functional

Paper: `papers/tex/Full_GR_From_Cost_Functional.tex`
Public repo: `github.com/jonwashburn/recognition-science`
Generated: 2026-03-30

## Direct Paper Roots (9 modules)

These modules are explicitly cited via `\leanref{}` in the paper.

| # | Module | Paper section |
|---|--------|---------------|
| 1 | `RecognitionScience.Foundation.ContinuumLimit` | Sec 2 (Cost Functional) |
| 2 | `RecognitionScience.Gravity.LatticeConvergence` | Sec 2 (Continuum convergence) |
| 3 | `RecognitionScience.Gravity.Connection` | Sec 3 (Metric & Christoffel) |
| 4 | `RecognitionScience.Gravity.RiemannTensor` | Sec 3 (Riemann tensor) |
| 5 | `RecognitionScience.Gravity.RicciTensor` | Sec 3 (Ricci/Einstein) |
| 6 | `RecognitionScience.Gravity.EinsteinHilbertAction` | Sec 4 (EH action) |
| 7 | `RecognitionScience.Gravity.StressEnergyTensor` | Sec 5 (Conservation) |
| 8 | `RecognitionScience.Gravity.ReggeConvergence` | Sec 6 (Regge convergence) |
| 9 | `RecognitionScience.Gravity.FullEFE` | Sec 7 (Master certificate) |

## Transitive Local Dependencies (18 modules)

These are imported transitively by the 9 roots above.

| # | Module | Required by |
|---|--------|-------------|
| 10 | `RecognitionScience.Constants` | Connection, RiemannTensor, RicciTensor, EH, Stress, Regge, FullEFE, LatticeConv, ZeroPG, PhiForcingDerived, TimeEmergence |
| 11 | `RecognitionScience.Cost` | ContinuumLimit, ZeroPG, LawOfExistence, Convexity, all Foundation |
| 12 | `RecognitionScience.Cost.Convexity` | ContinuumLimit, Thermodynamics, MeasurementMech, VariationalDyn, Determinism |
| 13 | `RecognitionScience.Foundation.LawOfExistence` | ContinuumLimit, ZeroPG, PhiForcing, DiscretenessForcing, InitialCond, etc. |
| 14 | `RecognitionScience.Foundation.InitialCondition` | ContinuumLimit, Thermodynamics, MeasurementMech, VariationalDyn |
| 15 | `RecognitionScience.Foundation.DiscretenessForcing` | ContinuumLimit, Thermodynamics, PhiForcing |
| 16 | `RecognitionScience.Foundation.Determinism` | MeasurementMech, VariationalDyn |
| 17 | `RecognitionScience.Foundation.PhiForcingDerived` | PhiForcing |
| 18 | `RecognitionScience.Foundation.PhiForcing` | DimensionForcing |
| 19 | `RecognitionScience.Foundation.DimensionForcing` | ContinuumLimit, ZeroPG, TimeEmergence |
| 20 | `RecognitionScience.Foundation.TimeEmergence` | MeasurementMech, VariationalDyn |
| 21 | `RecognitionScience.Foundation.VariationalDynamics` | ContinuumLimit, Thermodynamics, MeasurementMech |
| 22 | `RecognitionScience.Foundation.MeasurementMechanism` | Thermodynamics |
| 23 | `RecognitionScience.Foundation.Thermodynamics` | ContinuumLimit |
| 24 | `RecognitionScience.Gravity.ReggeCalculus` | FullEFE, DiscreteBianchi, NonlinearConv, ReggeConv |
| 25 | `RecognitionScience.Gravity.ZeroParameterGravity` | FullEFE |
| 26 | `RecognitionScience.Gravity.DiscreteBianchi` | FullEFE |
| 27 | `RecognitionScience.Gravity.NonlinearConvergence` | FullEFE |

## Full File List (27 files)

```
RecognitionScience/Constants.lean
RecognitionScience/Cost.lean
RecognitionScience/Cost/Convexity.lean
RecognitionScience/Foundation/LawOfExistence.lean
RecognitionScience/Foundation/InitialCondition.lean
RecognitionScience/Foundation/DiscretenessForcing.lean
RecognitionScience/Foundation/Determinism.lean
RecognitionScience/Foundation/PhiForcingDerived.lean
RecognitionScience/Foundation/PhiForcing.lean
RecognitionScience/Foundation/DimensionForcing.lean
RecognitionScience/Foundation/TimeEmergence.lean
RecognitionScience/Foundation/VariationalDynamics.lean
RecognitionScience/Foundation/MeasurementMechanism.lean
RecognitionScience/Foundation/Thermodynamics.lean
RecognitionScience/Foundation/ContinuumLimit.lean
RecognitionScience/Gravity/Connection.lean
RecognitionScience/Gravity/RiemannTensor.lean
RecognitionScience/Gravity/RicciTensor.lean
RecognitionScience/Gravity/EinsteinHilbertAction.lean
RecognitionScience/Gravity/StressEnergyTensor.lean
RecognitionScience/Gravity/LatticeConvergence.lean
RecognitionScience/Gravity/ReggeCalculus.lean
RecognitionScience/Gravity/ZeroParameterGravity.lean
RecognitionScience/Gravity/DiscreteBianchi.lean
RecognitionScience/Gravity/NonlinearConvergence.lean
RecognitionScience/Gravity/ReggeConvergence.lean
RecognitionScience/Gravity/FullEFE.lean
```

## Public Repo Status

Already public (16):
- `RecognitionScience/Constants.lean`
- `RecognitionScience/Cost.lean`
- `RecognitionScience/Cost/Convexity.lean`
- `RecognitionScience/Foundation/LawOfExistence.lean`
- `RecognitionScience/Foundation/InitialCondition.lean`
- `RecognitionScience/Foundation/DiscretenessForcing.lean`
- `RecognitionScience/Foundation/Determinism.lean`
- `RecognitionScience/Foundation/PhiForcingDerived.lean`
- `RecognitionScience/Foundation/PhiForcing.lean`
- `RecognitionScience/Foundation/DimensionForcing.lean`
- `RecognitionScience/Foundation/TimeEmergence.lean`
- `RecognitionScience/Foundation/VariationalDynamics.lean`
- `RecognitionScience/Foundation/MeasurementMechanism.lean`
- `RecognitionScience/Foundation/Thermodynamics.lean`
- `RecognitionScience/Foundation/ContinuumLimit.lean`
- `RecognitionScience/Gravity/ZeroParameterGravity.lean`

Must publish (11):
- `RecognitionScience/Gravity/Connection.lean`
- `RecognitionScience/Gravity/RiemannTensor.lean`
- `RecognitionScience/Gravity/RicciTensor.lean`
- `RecognitionScience/Gravity/EinsteinHilbertAction.lean`
- `RecognitionScience/Gravity/StressEnergyTensor.lean`
- `RecognitionScience/Gravity/LatticeConvergence.lean`
- `RecognitionScience/Gravity/ReggeCalculus.lean`
- `RecognitionScience/Gravity/DiscreteBianchi.lean`
- `RecognitionScience/Gravity/NonlinearConvergence.lean`
- `RecognitionScience/Gravity/ReggeConvergence.lean`
- `RecognitionScience/Gravity/FullEFE.lean`
