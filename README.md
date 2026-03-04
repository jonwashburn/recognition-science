# Recognition Science — Lean 4 Formalization

A machine-verified derivation of fundamental physics from a single functional equation.

## What This Is

This repository contains **Lean 4** proofs (built on [Mathlib](https://github.com/leanprover-community/mathlib4)) that derive:

- **The fine-structure constant** α⁻¹ ≈ 137.036 from cube geometry
- **All 12 fermion masses** (electron, muon, tau; 6 quarks; 3 neutrinos) from the φ-ladder
- **Newton's gravitational constant** G and the Einstein coupling κ = 8φ⁵
- **Three generations**, **three quark colors**, and the **mass hierarchy** from D = 3

All from a single starting point: the **Recognition Composition Law** (RCL).

## The Logical Chain

```
RCL: F(xy) + F(x/y) = 2F(x)F(y) + 2F(x) + 2F(y)
  ↓ d'Alembert uniqueness
J(x) = ½(x + x⁻¹) − 1                          [unique cost functional]
  ↓ self-similar closure
φ = (1+√5)/2                                      [golden ratio as hierarchy base]
  ↓ Hamiltonian cycle on Q₃
T_min = 2³ = 8                                    [8-tick fundamental period]
  ↓ combinatorial identity W_endo(D) = 17 ⟺ D = 3
V=8, E=12, F=6, A=1, E_pass=11, W=17             [cube integers]
  ↓ master mass law
m = A_s · φ^(r − 8 + gap(Z))                     [all fermion masses]
  ↓ Planck identity
κ = 8φ⁵, G = λ²c³/(πℏ)                           [gravity from φ]
```

**Zero adjustable parameters.** Every prediction is a definite function of φ and the integers of the 3-cube.

## Repository Structure

```
RecognitionScience/
├── Constants.lean              # φ, ℏ = φ⁻⁵, G, κ = 8φ⁵
├── Constants/
│   ├── AlphaDerivation.lean    # α⁻¹ from cube geometry (11, 103/102)
│   ├── FineStructureConstant.lean
│   └── GapWeight.lean          # w₈ DFT projection weight
├── Cost.lean                   # J(x) = ½(x + x⁻¹) − 1
├── Cost/
│   ├── FunctionalEquation.lean # RCL → d'Alembert → J uniqueness
│   ├── JcostCore.lean          # Core J-cost properties
│   ├── Convexity.lean
│   └── Calibration.lean
├── Foundation/
│   ├── LogicFromCost.lean      # T0: Logic from cost minimization
│   ├── PhiForcing.lean         # T6: φ² = φ + 1 from self-similarity
│   ├── EightTick.lean          # T7: 8-tick period, spin-statistics
│   ├── DimensionForcing.lean   # T8: D = 3 from W_endo = 17
│   ├── DAlembert/              # RCL inevitability proofs
│   ├── TimeEmergence.lean      # Arrow of time
│   ├── InitialCondition.lean   # Low-entropy initial state
│   ├── ParticleGenerations.lean # 3 generations from D = 3
│   ├── QuarkColors.lean        # 3 colors from D = 3
│   ├── HierarchyDissolution.lean
│   ├── Determinism.lean
│   └── UnifiedForcingChain.lean # T0–T8 chain
├── Masses/
│   ├── MassLaw.lean            # m = A_s · φ^(r−8+gap(Z))
│   ├── BaselineDerivation.lean # r_e=2, r_q=4, r_ν=−54 from cube
│   ├── Anchor.lean             # Sector yardsticks from cube formulas
│   ├── GapFunctionForcing.lean # gap(Z) = log_φ(1+Z/φ) uniqueness
│   ├── MassRatiosProved.lean   # Mass ratios = φ^(rung difference)
│   └── ZMapForcing.lean        # Charge index Z-map
├── Gravity/
│   ├── ZeroParameterGravity.lean # κ = 8φ⁵, equivalence principle
│   ├── EquivalencePrinciple.lean
│   ├── NoGraviton.lean         # Gravity is emergent, not mediated
│   ├── PropagationSpeed.lean   # c_grav = c (exact)
│   ├── ILGDerivation.lean      # Inherent Lattice Gravity
│   └── GravityDerivation.lean  # Complete G-001 through G-007
└── Unification/
    ├── RSMasterTheorem.lean    # Master theorem
    └── AllConstantsFromPhi.lean # All constants from φ
```

## Key Theorems

| Theorem | File | What it proves |
|---------|------|----------------|
| `phi_sq_eq` | Constants | φ² = φ + 1 |
| `phi_irrational` | Constants | φ is irrational |
| `kappa_einstein_eq` | Constants | κ = 8φ⁵ |
| `geometric_seed_eq` | AlphaDerivation | α⁻¹ seed = 4π·11 |
| `passive_edges_at_D3` | AlphaDerivation | Passive edges = 11 |
| `nontriviality_from_cost` | BaselineDerivation | J(x) > 0 ⟹ x ≠ 1 |
| `lepton_baseline_eq` | BaselineDerivation | r_e = A+1 = 2 |
| `quark_baseline_eq` | BaselineDerivation | r_q = 2^(D−1) = 4 |
| `neutrino_baseline_eq` | BaselineDerivation | r_ν = −(V+E+F+E_pass+W) = −54 |
| `predict_mass_pos` | MassLaw | All predicted masses are positive |
| `mass_rung_scaling` | MassLaw | m(r+1) = φ·m(r) |
| `gap_zero_neutral` | MassLaw | gap(0) = 0 (neutrino simplification) |
| `generation_ordering` | BaselineDerivation | 0 < E_pass < W |
| `affine_log_parameters_forced` | GapFunctionForcing | Three-point calibration forces gap function |

## Building

```bash
# Install Lean 4 (elan)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Clone and build
git clone https://github.com/jonwashburn/recognition-science.git
cd recognition-science
lake exe cache get    # download pre-built Mathlib (~2GB)
lake build            # build Recognition Science modules
```

## Zero Sorry, Zero Axioms*

Every theorem in this repository is fully proved — no `sorry` placeholders.

*One axiom is used: `aczel_representation_axiom` in `Cost/FunctionalEquation.lean`, which encodes the Aczél smoothness condition for the d'Alembert functional equation. This is a standard result in functional equation theory (Aczél, 1966).

## Papers

- Washburn, J. (2026). "Particle Masses from First Principles: A Complete Derivation of the Fermion Spectrum from the Recognition Composition Law."
- Washburn, J. (2026). "Inevitability from Three Attributes."

## License

MIT License — see [LICENSE](LICENSE).

## Author

Jonathan Washburn — Recognition Science Research Institute, Austin, Texas
