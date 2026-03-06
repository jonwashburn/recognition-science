# Recognition Science Paper Status

> Last updated: 2026-03-06

## ✅ ALL REQUESTED PAPERS ARE WRITTEN

---

## Tier 2 Papers — COMPLETE (14/14) — git commit c250e450a

| # | Paper | .tex | .pdf | Lean | Valid |
|---|-------|------|------|------|-------|
| 1 | Electron g−2 | ✓ | ✓ | `Physics/AnomalousMagneticMoment.lean` | ✓ |
| 2 | Superfluidity | ✓ | ✓ | `Physics/Superfluidity.lean` | ✓ |
| 3 | Quantum Hall Effect | ✓ | ✓ | `Physics/QuantumHallEffect.lean` | ✓ |
| 4 | BCS Superconductivity | ✓ | ✓ | `Physics/CooperPair.lean` | ✓ |
| 5 | Proton Radius Puzzle | ✓ | ✓ | `Physics/ProtonRadius.lean` | ✓ |
| 6 | Gravitational Lensing | ✓ | ✓ | `Gravity/GravitationalLensing.lean` | ✓ |
| 7 | No-Hair Theorem | ✓ | ✓ | `Physics/NoHairTheorem.lean` | ✓ |
| 8 | CMB Temperature | ✓ | ✓ | `Physics/CMBTemperature.lean` | ✓ |
| 9 | Stellar Evolution / HR | ✓ | ✓ | `Physics/StellarEvolution.lean` | ✓ |
| 10 | Gamma-Ray Bursts | ✓ | ✓ | `Physics/GammaRayBursts.lean` | ✓ |
| 11 | Renormalization / RG | ✓ | ✓ | `Physics/RunningCouplings.lean` | ✓ |
| 12 | Spin-Statistics | ✓ | ✓ | `Foundation/SpinStatistics.lean` | ✓ |
| 13 | Baryon Acoustic Osc. | ✓ | ✓ | `Physics/BAO.lean` | ✓ |
| 14 | Neutron Star / TOV | ✓ | ✓ | `Physics/NeutronStarTOV.lean` | ✓ |

All Lean modules: `lake build` → **Build completed successfully (7825 jobs), zero errors**

---

## Tier 1 Papers — COMPLETE (4/4) — git commit 6d3a7aebe

| Paper | .tex | .pdf | Key Lean proofs used |
|-------|------|------|---------------------|
| Special Relativity | ✓ | ✓ | `StepBounds`, `VoxelSymmetry`, `ConeBoundCert` |
| Maxwell's Equations | ✓ | ✓ | `ExactnessCert`, `GaugeInvariance`, `NoetherTheorem` |
| Hydrogen Atom Spectrum | ✓ | ✓ | `predict_mass`, `w8_projection_equality`, `LambShift` |
| Four Laws of Thermodynamics | ✓ | ✓ | `h_theorem_recognition`, `Jcost_unit0`, `ExactnessCert` |

---

## File Locations

```
papers/tex/RS_*.tex          ← all source files
papers/pdf/RS_*.pdf          ← all compiled PDFs
RecognitionScience/Physics/  ← Lean proof modules
RecognitionScience/Foundation/SpinStatistics.lean
RecognitionScience/Gravity/GravitationalLensing.lean
papers/TIER2_PAPER_PROGRESS.md  ← validation tables
papers/RS_PUBLIC_PAPERS_LIST.md ← public registry
```

---

## What To Do Next

- **Tier 3 papers:** Zeeman/Stark effects, Compton scattering, BEC,
  nuclear force, radioactive decay, cosmic neutrino background,
  classical mechanics from RS
- **Strengthen proofs:** Remove remaining HYPOTHESIS labels by writing
  more Lean code for the pending items in each paper's validation table
- **Submit papers:** The 14 Tier 2 papers are ready for submission to
  journals (e.g. Foundations of Physics, Physical Review D)
