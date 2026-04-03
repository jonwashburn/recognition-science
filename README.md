# Recognition Science — Lean 4 Formalization

A Lean 4 formalization and certificate suite centered on a single functional equation.

## What This Is

This repository contains **Lean 4** proofs (built on [Mathlib](https://github.com/leanprover-community/mathlib4)) that derive:

- **The fine-structure constant** α⁻¹ ≈ 137.036 from cube geometry
- **All 12 fermion masses** (electron, muon, tau; 6 quarks; 3 neutrinos) from the φ-ladder
- **Newton's gravitational constant** G and the Einstein coupling κ = 8φ⁵
- **Three generations**, **three quark colors**, and the **mass hierarchy** from D = 3

All from a single starting point: the **Recognition Composition Law** (RCL).

## Canonical Public Framework

The canonical public namespace is **`RecognitionScience`**.

This matches the namespace used throughout the submitted JAR paper:
Simons, M. and Washburn, J.,
*Certificate-Based Verification of Derivation-Graph Structural Properties
in Lean 4/Mathlib*.
That paper references paths such as
`RecognitionScience.Cost.FunctionalEquation`,
`RecognitionScience.Masses.BaselineDerivation`, and the 36 verification
certificates under `RecognitionScience/Verification/`.

The `IndisputableMonolith/` tree is an **internal support library** for
structural certification, observable-payload types, and bridge modules.
It is not a second framework.

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

## Current Public Snapshot

The repaired public snapshot currently contains:

- **175 Lean files**
- **1,490 theorem/lemma declarations**
- **32,621 lines of Lean source**
- **36 verification certificate modules**
- A successful package-wide `lake build`

In this public snapshot:

- The historically named theorem `aczel_representation_axiom` is now **proved internally** in Lean.
- The **full d'Alembert inevitability chain** builds successfully, including `Foundation/DAlembert/FullUnconditional.lean`.
- The repository is **not yet globally `sorry`-free**; some peripheral modules still contain admitted placeholders.

## Repository Structure

```
RecognitionScience/
├── Constants/                        # 5 files
├── Cost/                             # 17 files
│   ├── AczelTheorem.lean             # Internal Aczél smoothness proof
│   ├── FunctionalEquation.lean       # RCL → d'Alembert → J uniqueness
│   ├── Convexity.lean                # J strict convexity
│   ├── Derivative.lean               # J derivatives and bounds
│   └── Ndim/                         # N-dimensional cost extension
├── Foundation/                       # 33 files
│   ├── DAlembert/
│   │   ├── Inevitability.lean        # Bilinear family forced
│   │   ├── DegreeExclusion.lean      # Degree-3 combiner exclusion
│   │   ├── WLOGAlphaOne.lean         # α-rescaling is WLOG
│   │   ├── Unconditional.lean        # P computed from J
│   │   └── FullUnconditional.lean    # Full inevitability chain
│   ├── UnifiedForcingChain.lean      # T0–T8 chain
│   └── ...                           # Additional foundation modules
├── Gravity/                          # 19 files
├── Masses/                           # 28 files
├── Numerics/                         # 12 files
├── Papers/                           # 4 files
├── Physics/                          # 14 files
├── Patterns/                         # 1 file
├── Derivations/                      # 1 file
├── Unification/                      # 2 files
├── Verification/                     # 36 certificate modules
├── Cost.lean                         # Root namespace module
├── Constants.lean                    # Root namespace module
└── Patterns.lean                     # Root namespace module
```

`RecognitionScience/` is the canonical public namespace (matching the JAR paper).
`IndisputableMonolith/` is an internal support library for structural
certification and bridge modules.

---

## Verification Certificates

The `Verification/` directory contains **36 machine-checked certificate modules** — Lean structures that bundle related theorems and verify them in a single `verified` predicate. Each certificate is independently checkable.

### Master Certificates

| Certificate | What It Verifies |
|-------------|-----------------|
| **ForcingChainCert** | The **complete** T0–T8 → masses → gravity chain in one structure: J uniqueness, φ² = φ+1, T_min = 8, D = 3 cube integers, baseline rungs, mass positivity, φ-scaling, gap(0) = 0, κ = 8φ⁵ |
| **InevitabilityCert** | Every structural step is **unique** — no alternative exists: J is the only cost, φ is the only base, D = 3 is the only dimension, and every baseline rung is forced by cube geometry |
| **ExclusivityCert** | The framework is the **only** one producing this structure: φ exclusivity, dimension exclusivity, J strict positivity away from x = 1, mass φ-scaling |
| **NonCircularityCert** | The derivation is **non-circular**: all quantities (sector constants, baseline rungs, α integers, charge scale) trace to D = 3 cube combinatorics — no experimental data enters upstream |
| **Tier1Cert** | T0–T8 forcing chain bundle: meta-principle, recognition, ledger, cost uniqueness, φ uniqueness, 8-tick, D = 3 |
| **Tier2Cert** | All derived constants and mass predictions follow from Tier 1 |

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
lake build            # build both IndisputableMonolith and RecognitionScience
```

## Verification Status

- **175+ Lean files** in the current public snapshot
- **1,490+ theorem/lemma declarations**
- **36+ verification certificate modules**
- **Successful package-wide `lake build`**
- **Aczél smoothness internalized**: `aczel_representation_axiom` is now a theorem in `Cost/AczelTheorem.lean`
- **Full d'Alembert inevitability chain restored**: `Foundation/DAlembert/FullUnconditional.lean` builds successfully
- **Not yet globally `sorry`-free**: some peripheral modules still contain admitted placeholders

### JAR paper artifact

The JAR paper (Simons & Washburn) analyzes the `RecognitionScience` namespace
at commit `0f9fcbe8` (Lean `v4.29.0-rc6`, Mathlib `d7ea5678`). The public
export on this branch includes the same directory structure and certificates
described in that paper, plus recent additions (hierarchy modules, typed
observable payloads, structural derivation certificates) from the ongoing
formalization effort.

## Papers

- Simons, M. and Washburn, J. (2026). *Certificate-Based Verification of Derivation-Graph Structural Properties in Lean 4/Mathlib.* Submitted to Journal of Automated Reasoning. This is the canonical paper for this repository; the `RecognitionScience` namespace matches the artifact analyzed in that paper.
- Washburn, J. and Zlatanović, M. (2026). [*Uniqueness of the Canonical Reciprocal Cost.*](https://doi.org/10.3390/axioms15020090) Axioms (MDPI), March 2026.
- Washburn, J. (2026). *Particle Masses from First Principles: A Complete Derivation of the Fermion Spectrum from the Recognition Composition Law.*
- Washburn, J. (2026). *Inevitability from Three Attributes.*

## License

MIT License — see [LICENSE](LICENSE).

## Author

Jonathan Washburn — [Recognition Science Institute](https://recognitionphysics.org), Austin, Texas
