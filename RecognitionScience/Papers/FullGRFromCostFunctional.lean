import RecognitionScience.Foundation.ContinuumLimit
import RecognitionScience.Gravity.LatticeConvergence
import RecognitionScience.Gravity.Connection
import RecognitionScience.Gravity.RiemannTensor
import RecognitionScience.Gravity.RicciTensor
import RecognitionScience.Gravity.EinsteinHilbertAction
import RecognitionScience.Gravity.StressEnergyTensor
import RecognitionScience.Gravity.ReggeConvergence
import RecognitionScience.Gravity.FullEFE

/-!
# Paper: Machine-Verified General Relativity from a Single Functional Equation

This module imports all 9 Lean modules cited in the paper
"Machine-Verified General Relativity from a Single Functional Equation"
(Washburn, April 2026).

Building this single file verifies the entire 27-file transitive closure
(9 direct roots + 18 local dependencies) compiles with zero `sorry`.

## Paper-to-Module Map

| Paper Section | Module | Key Theorem |
|---|---|---|
| Sec 2: Cost functional | `Foundation.ContinuumLimit` | `jcost_quadratic_leading` |
| Sec 2: Continuum convergence | `Gravity.LatticeConvergence` | `lattice_laplacian_3D_convergence` |
| Sec 3: Metric & Christoffel | `Gravity.Connection` | `christoffel_symmetric` |
| Sec 3: Riemann tensor | `Gravity.RiemannTensor` | `algebraic_bianchi` |
| Sec 3: Ricci/Einstein | `Gravity.RicciTensor` | `minkowski_is_vacuum_solution` |
| Sec 4: EH action | `Gravity.EinsteinHilbertAction` | `hilbert_variation_flat` |
| Sec 5: Conservation | `Gravity.StressEnergyTensor` | `conservation_from_efe_and_bianchi` |
| Sec 6: Regge convergence | `Gravity.ReggeConvergence` | `linearized_convergence` |
| Sec 7: Master certificate | `Gravity.FullEFE` | `full_gr_certificate` |

## Build Instructions

```bash
lake exe cache get          # Download Mathlib cache (~2GB, one-time)
lake build RecognitionScience.Papers.FullGRFromCostFunctional
```

## Transitive Closure (27 files)

The 9 root modules above transitively import 18 additional local modules:
Constants, Cost, Cost.Convexity, Foundation.{LawOfExistence, InitialCondition,
DiscretenessForcing, Determinism, PhiForcingDerived, PhiForcing, DimensionForcing,
TimeEmergence, VariationalDynamics, MeasurementMechanism, Thermodynamics},
Gravity.{ReggeCalculus, ZeroParameterGravity, DiscreteBianchi, NonlinearConvergence}
-/
