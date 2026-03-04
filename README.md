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

---

## Repository Structure

```
RecognitionScience/
├── Constants.lean                    # φ, ℏ = φ⁻⁵, G, κ = 8φ⁵
├── Cost.lean                         # J(x) = ½(x + x⁻¹) − 1
├── Constants/
│   ├── AlphaDerivation.lean          # α⁻¹ from cube geometry
│   ├── FineStructureConstant.lean    # α properties
│   └── GapWeight.lean                # w₈ DFT projection weight
├── Cost/
│   ├── FunctionalEquation.lean       # RCL → d'Alembert → J uniqueness
│   ├── JcostCore.lean                # J-cost core properties
│   ├── Convexity.lean                # J convexity
│   └── Calibration.lean              # λ=1 calibration
├── Foundation/
│   ├── LogicFromCost.lean            # T0: Logic from cost
│   ├── PhiForcing.lean               # T6: φ² = φ + 1
│   ├── EightTick.lean                # T7: 8-tick period, spin-statistics
│   ├── DimensionForcing.lean         # T8: D = 3
│   ├── DAlembert/                    # RCL inevitability proofs
│   ├── TimeEmergence.lean            # Arrow of time
│   ├── InitialCondition.lean         # Low-entropy initial state
│   ├── ParticleGenerations.lean      # 3 generations from D = 3
│   ├── QuarkColors.lean              # 3 colors from D = 3
│   ├── HierarchyDissolution.lean     # No hierarchy problem
│   ├── Determinism.lean              # Determinism from J-cost
│   └── UnifiedForcingChain.lean      # T0–T8 chain
├── Masses/                           # 26 files — complete mass framework
│   ├── MassLaw.lean                  # m = A_s · φ^(r−8+gap(Z))
│   ├── BaselineDerivation.lean       # r_e=2, r_q=4, r_ν=−54
│   ├── Anchor.lean                   # Sector yardsticks from cube geometry
│   ├── AnchorDerivation.lean         # Full anchor chain derivation
│   ├── GapFunctionForcing.lean       # gap(Z) = log_φ(1+Z/φ) uniqueness
│   ├── MassRatiosProved.lean         # Mass ratios = φ^Δr
│   ├── MassHierarchy.lean            # Mass hierarchy structure
│   ├── LeptonMassLadder.lean         # e/μ/τ mass ladder
│   ├── JCostPerturbation.lean        # J-cost perturbation theory (1633 lines)
│   ├── CoherenceExponent.lean        # E_coh = φ⁻⁵ derivation
│   ├── ZMapForcing.lean              # Charge index Z-map
│   ├── RungConstructor/              # Rung construction machinery
│   ├── Ribbons/                      # Ribbon algebra for mass braids
│   └── ...                           # + 13 more supporting modules
├── Gravity/                          # 18 files — complete gravity framework
│   ├── ZeroParameterGravity.lean     # κ = 8φ⁵, equivalence principle
│   ├── EquivalencePrinciple.lean     # m_inertial = m_grav
│   ├── NoGraviton.lean               # Gravity is emergent
│   ├── PropagationSpeed.lean         # c_grav = c (exact)
│   ├── ILG.lean                      # Inherent Lattice Gravity core
│   ├── ILGDerivation.lean            # ILG time-kernel, flat rotation curves
│   ├── GravityDerivation.lean        # G-001 through G-007
│   ├── GravityParameters.lean        # Complete parameter table (340 lines)
│   ├── RunningG.lean                 # Running gravitational coupling
│   ├── RunningGDerivation.lean       # Running G derivation chain
│   ├── RotationILG.lean              # Galaxy rotation from ILG
│   ├── BTFREmergence.lean            # Baryonic Tully-Fisher emergence
│   ├── RAREmergence.lean             # Radial Acceleration Relation
│   ├── CausalKernelChain.lean        # Causal kernel structure (305 lines)
│   └── ...                           # + 4 more supporting modules
├── Cost/
│   ├── FunctionalEquation.lean       # RCL → d'Alembert → J uniqueness
│   ├── JcostCore.lean                # J-cost core properties
│   ├── AczelTheorem.lean             # Aczél smoothness theorem
│   ├── Convexity.lean                # J strict convexity
│   ├── Derivative.lean               # J derivatives and bounds
│   ├── ClassicalResults.lean         # Classical functional equation results
│   ├── Ndim/                         # N-dimensional cost extension (9 files)
│   └── ...                           # Calibration, FixedPoint
├── Physics/
│   ├── ForcingChainUnification.lean  # Cost–φ consistency, zero-parameter structure
│   └── ThreeGenerations.lean         # Three generations from D = 3
├── Patterns/
│   ├── GrayCycle.lean                # Gray code Hamiltonian cycle on Q₃
│   └── ...                           # Pattern infrastructure
├── Derivations/
│   └── MassToLight.lean              # φ-power mass-to-light bridge
├── Unification/
│   ├── RSMasterTheorem.lean          # Master theorem
│   └── AllConstantsFromPhi.lean      # All constants from φ
└── Verification/                     # 32 machine-checked certificates
    ├── Tier1Cert.lean                # T0–T8 forcing chain
    ├── Tier2Cert.lean                # Constants + masses
    └── ...                           # See certificate catalog below
```

---

## Verification Certificates

The `Verification/` directory contains **32 machine-checked certificates** — Lean structures that bundle related theorems and verify them in a single `verified` predicate. Each certificate is independently checkable.

### Tier Certificates (Integration Bundles)

| Certificate | What It Verifies |
|-------------|-----------------|
| **Tier1Cert** | Complete T0–T8 forcing chain: meta-principle, recognition structure, ledger forcing, cost uniqueness (J = cosh), φ uniqueness, 8-tick period with minimality bound, D = 3 dimension rigidity |
| **Tier2Cert** | All derived constants and mass predictions follow from the Tier 1 foundation |

### Cost Functional Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **JcostNormalizationCert** | J(1) = 0 — zero cost at the identity ratio |
| **JcostMinimumCert** | J(x) ≥ 0 for all x > 0 — cost is non-negative (AM-GM) |
| **JcostMonoCert** | J is strictly monotone on (0,1) and (1,∞) |
| **JcostCoshFormCert** | J(x) = cosh(ln x) − 1 — explicit hyperbolic form |
| **JcostAxiomsCert** | All J-cost axioms (symmetry, normalization, positivity) hold simultaneously |
| **JCostAtPhiCert** | J evaluated at φ gives the specific value J(φ) = (φ + φ⁻¹)/2 − 1 |
| **CalibrationCert** | The calibration condition λ = 1 (unit curvature at x = 1) is consistent |
| **UnitNormalizationZeroCert** | F(1) = 0 normalization verified |
| **DAlembertSymmetryCert** | The d'Alembert functional equation inherits reciprocal symmetry from the RCL |
| **ODECoshUniqueCert** | The ODE y'' = y with y(0) = 1, y'(0) = 0 has unique solution cosh(t) |
| **ODEFoundationCert** | Foundation-level ODE existence and uniqueness for the cost functional |

### Golden Ratio Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **PhiFixedPointCert** | φ = 1 + 1/φ — the self-referential fixed-point equation |
| **PhiIrrationalityCert** | φ is irrational (via irrationality of √5) |
| **PhiDecimalBoundsCert** | 1.5 < φ < 1.62 — tight decimal bounds |
| **PhiPowerBoundsCert** | Bounds on φ², φ³, φ⁴, φ⁵ — Fibonacci power identities |
| **PhiNecessityCert** | φ is the *unique* positive solution of x² = x + 1 |
| **PhiNonDegenerateCert** | φ ≠ 0, φ ≠ 1, φ > 1 — non-degeneracy conditions |

### Cube Geometry & Alpha Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **CubeGeometryCert** | All "magic numbers" from D = 3: V = 8, E = 12, F = 6, E_pass = 11, 102 = 6×17, 103 = 6×17+1, wallpaper groups = 17, Euler closure = 1. Proves each integer is forced by cube combinatorics |
| **EightTickLowerBoundCert** | T_min ≥ 8 — the 8-tick period is the minimum for the 3-cube |
| **RootsOfUnitySumCert** | The sum of the 8th roots of unity equals zero |
| **EMAlphaCert** | α⁻¹ ≈ 137.036 derived from geometric seed (4π·11), gap weight, and exponential resummation. Verifies the numerical range 137.030 < α⁻¹ < 137.039 |
| **HighPrecisionCert** | Extended precision verification of α⁻¹ |
| **GapWeightDerivationCert** | The DFT-8 gap weight w₈ derivation chain is consistent |

### Structural & Closure Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **ZeroAdjustableParamsCert** | knobsCount = 0 — the framework has exactly zero continuously adjustable parameters |
| **HonestClosureCert** | Honest accounting of all boundary inputs — nothing is hidden |
| **StructuralDerivationGapCert** | The gap function derivation chain (g(0) = 0, g(1) = 1, g(−1) = −2 → gap = log_φ(1+Z/φ)) is internally consistent |
| **StructuralPartitionCert** | The sector partition into lepton/up-quark/down-quark/electroweak is exhaustive |

### Physics Prediction Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **RSPhysicalModelCert** | The complete RS physical model (cost functional + φ-ladder + cube geometry) is internally consistent |
| **ParticlePhysicsCert** | Particle physics predictions (mass law, sector structure, generation counting) are derived from the forcing chain |
| **NeutrinoSectorCert** | Neutrino sector predictions (mass ordering, rung structure, splittings) are consistent with the master mass law |
| **ILGAlphaCert** | Inherent Lattice Gravity is consistent with the α derivation — gravity and electromagnetism share the same cube-geometric origin |

---

## Key Theorems

| Theorem | File | What It Proves |
|---------|------|----------------|
| `phi_sq_eq` | Constants | φ² = φ + 1 |
| `phi_irrational` | Constants | φ is irrational |
| `kappa_einstein_eq` | Constants | κ = 8φ⁵ |
| `hbar_eq_phi_inv_fifth` | Constants | ℏ = φ⁻⁵ |
| `geometric_seed_eq` | AlphaDerivation | α⁻¹ geometric seed = 4π·11 |
| `passive_edges_at_D3` | AlphaDerivation | Passive edges = 11 |
| `eleven_is_forced` | AlphaDerivation | 11 = cube_edges(3) − 1 |
| `one_oh_three_is_forced` | AlphaDerivation | 103 = 6×17 + 1 |
| `nontriviality_from_cost` | BaselineDerivation | J(x) > 0 ⟹ x ≠ 1 |
| `lepton_baseline_eq` | BaselineDerivation | r_e = A + 1 = 2 |
| `quark_baseline_eq` | BaselineDerivation | r_q = 2^(D−1) = 4 |
| `neutrino_baseline_eq` | BaselineDerivation | r_ν = −(V+E+F+E_pass+W) = −54 |
| `octave_offset_eq` | BaselineDerivation | Octave offset = −T_min = −8 |
| `generation_ordering` | BaselineDerivation | 0 < E_pass < W (0 < 11 < 17) |
| `predict_mass_pos` | MassLaw | All predicted masses are positive |
| `mass_rung_scaling` | MassLaw | m(r+1) = φ · m(r) |
| `gap_zero_neutral` | MassLaw | gap(0) = 0 (neutrino simplification) |
| `affine_log_parameters_forced` | GapFunctionForcing | Three-point calibration uniquely fixes gap function |
| `mass_ratio_from_rung_difference` | MassRatiosProved | m₂/m₁ = φ^(r₂−r₁) |
| `kappa_rs_closed_form` | ZeroParameterGravity | κ = 8φ⁵ |
| `c_grav_eq_c_RS` | PropagationSpeed | c_grav = c (exact equality) |

---

## Building

```bash
# Install Lean 4 via elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Clone and build
git clone https://github.com/jonwashburn/recognition-science.git
cd recognition-science
lake exe cache get    # download pre-built Mathlib (~2GB, saves hours)
lake build            # build all Recognition Science modules
```

## Verification Status

- **122 Lean files** across 10 directories
- **90 core derivation modules** + **32 verification certificates**
- **Zero `sorry`** — every theorem is fully proved
- **Zero forbidden placeholders** — no `admit`, no `native_decide` on non-decidable propositions

One axiom is used: `aczel_representation_axiom` in `Cost/FunctionalEquation.lean`, encoding the Aczél smoothness condition for the d'Alembert functional equation (a standard result in functional equation theory; Aczél, 1966).

## Papers

- Washburn, J. (2026). *Particle Masses from First Principles: A Complete Derivation of the Fermion Spectrum from the Recognition Composition Law.*
- Washburn, J. (2026). *Inevitability from Three Attributes.*

## License

MIT License — see [LICENSE](LICENSE).

## Author

Jonathan Washburn — [Recognition Science Institute](https://recognitionphysics.org), Austin, Texas
