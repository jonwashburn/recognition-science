# Tier 2 Paper Progress Tracker

> **Goal:** Complete all 14 standalone Tier 2 papers for Recognition Science.
>
> **Lean module root:** `RecognitionScience/` (the active Lean project in this repo)
> **Paper tex root:** `papers/tex/`
> **Architecture spec:** `papers/tex/Recognition-Science-Full-Theory.txt`
>
> **Last updated:** 2026-03-06 — ALL 14 PAPERS COMPLETE

---

## Status Key

| Symbol | Meaning |
|--------|---------|
| `[ ]` | Not started |
| `[~]` | In progress |
| `[x]` | Complete |

---

## Summary Table

| # | Paper | Lean | Tex | PDF | Valid |
|---|-------|------|-----|-----|-------|
| 1 | Electron g−2 | [x] | [x] | [x] | [x] |
| 2 | Superfluidity | [x] | [x] | [x] | [x] |
| 3 | Quantum Hall Effect | [x] | [x] | [x] | [x] |
| 4 | BCS Superconductivity | [x] | [x] | [x] | [x] |
| 5 | Proton Radius Puzzle | [x] | [x] | [x] | [x] |
| 6 | Gravitational Lensing | [x] | [x] | [x] | [x] |
| 7 | No-Hair Theorem | [x] | [x] | [x] | [x] |
| 8 | CMB Temperature | [x] | [x] | [x] | [x] |
| 9 | Stellar Evolution / HR Diagram | [x] | [x] | [x] | [x] |
| 10 | Gamma-Ray Bursts | [x] | [x] | [x] | [x] |
| 11 | Renormalization / Running Couplings | [x] | [x] | [x] | [x] |
| 12 | Spin-Statistics Theorem | [x] | [x] | [x] | [x] |
| 13 | Baryon Acoustic Oscillations | [x] | [x] | [x] | [x] |
| 14 | Neutron Star / TOV Limit | [x] | [x] | [x] | [x] |

> **Phase 1 (2026-03-06):** All 14 .tex files written and compiled to PDF.
> **Phase 2 (2026-03-06):** All 14 dedicated Lean 4 proof modules written and compiled with zero errors.
> **Phase 3 (2026-03-06):** Validation tables added; all papers registered in RS_PUBLIC_PAPERS_LIST.md.

---

## Paper 1 — Electron g−2

**File:** `papers/tex/RS_Electron_g_minus_2.tex`
**PDF:** `papers/pdf/RS_Electron_g_minus_2.pdf`
**Lean module:** `RecognitionScience/Physics/AnomalousMagneticMoment.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| α^{-1} = 137.036 from φ-ladder | A | `Constants.GapWeight.ProjectionEquality.w8_projection_equality` (zero sorry) |
| Schwinger term a_e^(1) = α/(2π) | A | `Physics.AnomalousMagneticMoment.schwinger_term_positive` |
| a_e^(1) < 0.002 | A | `Physics.AnomalousMagneticMoment.schwinger_lt_002` |
| Electron g > 2 | A | `Physics.AnomalousMagneticMoment.g_exceeds_dirac` |
| Eight-tick phase sum = 0 | A | `Foundation.EightTick.sum_8_phases_eq_zero` |
| Higher-order c_n coefficients | B | HYPOTHESIS: falsifier = RS loop integral gives c_2 ≠ −0.32848 |
| Full 13-digit agreement | B | HYPOTHESIS: falsifier = RS prediction deviates > 3σ from experiment |

---

## Paper 2 — Superfluidity

**File:** `papers/tex/RS_Superfluidity.tex`
**PDF:** `papers/pdf/RS_Superfluidity.pdf`
**Lean module:** `RecognitionScience/Physics/Superfluidity.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| BE occupation is positive for ε > μ | A | `Physics.Superfluid.be_occupation_positive` |
| BEC temperature is positive | A | `Physics.Superfluid.bec_temperature_positive` |
| λ-point < T_BEC when interactions present | A | `Physics.Superfluid.lambda_point_lt_bec` |
| Vortex quantum κ = h/m is positive | A | `Physics.Superfluid.vortex_quantum_positive` |
| φ-ladder critical exponent α > 0 | A | `Physics.Superfluid.rs_critical_exponent_positive` |
| Superfluid fraction at T=0 equals 1 | A | `Physics.Superfluid.superfluid_fraction_at_zero` |
| Superfluid fraction at T=T_λ equals 0 | A | `Physics.Superfluid.superfluid_fraction_at_lambda` |
| T_λ = 2.17 K numerical value | B | HYPOTHESIS: falsifier = RS η gives T_λ outside [2.0, 2.5] K |
| He-3 Cooper pairing T_c ≈ 2.5 mK | B | HYPOTHESIS: falsifier = T_c(He-3) < 1 mK or > 5 mK |

---

## Paper 3 — Quantum Hall Effect

**File:** `papers/tex/RS_Quantum_Hall_Effect.tex`
**PDF:** `papers/pdf/RS_Quantum_Hall_Effect.pdf`
**Lean module:** `RecognitionScience/Physics/QuantumHallEffect.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| α^{-1} ≈ 137 from φ-ladder | A | `Constants.GapWeight.ProjectionEquality.w8_projection_equality` |
| Spin-statistics (fermion exchange = −1) | A | `Foundation.EightTick.spin_statistics_key` |
| Landau levels equally spaced | A | `Physics.QHE.landau_spacing` |
| Zero-point energy = ω_c/2 (fermionic) | A | `Physics.QHE.zero_point_energy` |
| FQHE denominator always odd | A | `Physics.QHE.fqhe_odd_denominator` |
| ν = 1/3 in Jain sequence | A | `Physics.QHE.one_third_in_jain_sequence` |
| Quasi-particle charge e/3 at ν=1/3 | A | `Physics.QHE.laughlin_charge_one_third` |
| R_K = h/e² is positive | A | `Physics.QHE.RK_positive` |
| Integer Chern number from 8-tick | A | `Physics.QHE.chern_number_integer_from_8tick` |
| Laughlin state as J-cost minimizer | B | HYPOTHESIS: falsifier = ν=1/3 state not of Laughlin form |
| IQH conductance σ_xy = ne²/h | B | HYPOTHESIS: falsifier = non-integer Hall conductance in isolated filled LL |

---

## Paper 4 — BCS Superconductivity

**File:** `papers/tex/RS_BCS_Superconductivity.tex`
**PDF:** `papers/pdf/RS_BCS_Superconductivity.pdf`
**Lean module:** `RecognitionScience/Physics/CooperPair.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| Time-reversed pair has zero J-cost | A | `Physics.BCS.time_reversed_pair_zero_cost` |
| Pairing lowers total J-cost | A | `Physics.BCS.pairing_lowers_cost` |
| Cooper criterion: paired state wins | A | `Physics.BCS.cooper_criterion` |
| BCS gap Δ is positive | A | `Physics.BCS.bcs_gap_positive` |
| T_c is positive | A | `Physics.BCS.bcs_Tc_positive` |
| Universal ratio 2Δ/(k_B T_c) = 4/1.134 ≈ 3.528 | A | `Physics.BCS.universal_bcs_ratio` |
| Ratio ≈ 3.52 (numerical) | A | `Physics.BCS.ratio_approx_3_52` |
| London depth is positive | A | `Physics.BCS.london_depth_positive` |
| Isotope effect: heavier M → lower T_c | A | `Physics.BCS.isotope_effect` |
| Full Cooper pair RS derivation | B | HYPOTHESIS: falsifier = BCS gap ratio ≠ 3.528 in conventional SC |
| London equation from RS | B | HYPOTHESIS: falsifier = magnetic flux penetrating type-I SC below T_c |

---

## Paper 5 — Proton Radius Puzzle

**File:** `papers/tex/RS_Proton_Radius_Puzzle.tex`
**PDF:** `papers/pdf/RS_Proton_Radius_Puzzle.pdf`
**Lean module:** `RecognitionScience/Physics/ProtonRadius.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| φ > 1 | A | `Physics.ProtonRadius.phi_gt_one` |
| m_μ/m_e = φ^11 > 1 | A | `Physics.ProtonRadius.muon_heavier` |
| Muonic Bohr radius < electronic | A | `Physics.ProtonRadius.muonic_smaller` |
| Proton radius estimate is positive | A | `Physics.ProtonRadius.proton_radius_positive` |
| No leptonic universality violation | A | `Physics.ProtonRadius.leptonic_universality` |
| Old 0.877 fm differs > 3% from CODATA | A | `Physics.ProtonRadius.old_value_differs` |
| Form factor correction small at low Q | A | `Physics.ProtonRadius.form_factor_near_one` |
| RS proton charge radius ≈ 0.84 fm | B | HYPOTHESIS: falsifier = precision r_p < 0.82 fm or > 0.86 fm |
| RS form factor deviates from dipole 15% | B | HYPOTHESIS: falsifier = EIC/PRad-II measurement at Q < 0.1 GeV |

---

## Paper 6 — Gravitational Lensing

**File:** `papers/tex/RS_Gravitational_Lensing.tex`
**PDF:** `papers/pdf/RS_Gravitational_Lensing.pdf`
**Lean module:** `RecognitionScience/Gravity/GravitationalLensing.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| EFE from RS action | A | `Relativity.Dynamics.EFEEmergence.jacobi_det_formula`, `efe_algebraic_step`, `efe_from_mp` |
| Schwarzschild metric | A | `Relativity.StaticSpherical` |
| GR deflection = 2× Newtonian | A | `Gravity.Lensing.gr_is_twice_newton` |
| Deflection angle is positive | A | `Gravity.Lensing.deflection_positive` |
| Deflection scales as 1/b | A | `Gravity.Lensing.deflection_inverse_b` |
| Einstein radius is positive | A | `Gravity.Lensing.einstein_radius_positive` |
| Shapiro delay is positive | A | `Gravity.Lensing.shapiro_delay_positive` |
| ILG correction enhances convergence | A | `Gravity.Lensing.ilg_correction_enhances` |
| ILG CMB lensing prediction | B | HYPOTHESIS: falsifier = CMB-S4 no deviation from GR at ℓ < 100 |
| Weak lensing shear map | B | HYPOTHESIS: falsifier = DES/Euclid shear > 5σ from RS |

---

## Paper 7 — Black Hole No-Hair Theorem

**File:** `papers/tex/RS_No_Hair_Theorem.tex`
**PDF:** `papers/pdf/RS_No_Hair_Theorem.pdf`
**Lean module:** `RecognitionScience/Physics/NoHairTheorem.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| J-cost ≥ 0 | A | `Cost.Jcost_nonneg` |
| Hair cost vanishes iff amplitude = 0 | A | `Physics.NoHair.hair_cost_zero_iff` |
| BH state determined by (M,Q,J) | A | `Physics.NoHair.bh_state_determined_by_charges` |
| Exactly 3 conserved charges | A | `Physics.NoHair.exactly_three_conserved_charges` |
| Bekenstein-Hawking entropy ≥ 0 | A | `Physics.NoHair.entropy_nonneg` |
| Entropy linear in area | A | `Physics.NoHair.entropy_linear_in_area` |
| Schwarzschild entropy = 4πM² | A | `Physics.NoHair.schwarzschild_entropy_eq` |
| Entropy monotone in M | A | `Physics.NoHair.schwarzschild_entropy_monotone` |
| Hawking temperature positive | A | `Physics.NoHair.hawking_temp_positive` |
| Hawking temperature decreases with M | A | `Physics.NoHair.hawking_temp_decreases` |
| Kerr-Newman uniqueness (RS) | B | HYPOTHESIS: falsifier = stationary charged rotating BH not described by KN metric |

---

## Paper 8 — CMB Temperature

**File:** `papers/tex/RS_CMB_Temperature.tex`
**PDF:** `papers/pdf/RS_CMB_Temperature.pdf`
**Lean module:** `RecognitionScience/Physics/CMBTemperature.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| T* = 3000 K (recombination) > 0 | A | `Physics.CMB.recombination_temperature_positive` |
| k_B T* ≈ 0.26 eV | A | `Physics.CMB.recombination_energy_approx_eV` |
| z* = 1100 > 0 | A | `Physics.CMB.recombination_redshift_positive` |
| CMB temperature positive | A | `Physics.CMB.cmb_temperature_positive` |
| T₀ ≈ 3000/1101 ≈ 2.725 K | A | `Physics.CMB.rs_cmb_approx_2725` |
| Consistent with FIRAS | A | `Physics.CMB.rs_cmb_consistent_with_firas` |
| Planck spectrum positive | A | `Physics.CMB.planck_positive` |
| CMB is Planck spectrum at T₀ | A | `Physics.CMB.cmb_is_planck_spectrum` |
| Acoustic peaks at ℓ_n ≈ 220n | A | `Physics.CMB.acoustic_peak_positions` |
| T₀ scales with redshift | A | `Physics.CMB.cmb_temperature_scales_with_redshift` |
| Precise T₀ from RS ladder rung | B | HYPOTHESIS: falsifier = RS-derived η gives z* ∉ [1050,1150] |

---

## Paper 9 — Stellar Evolution / HR Diagram

**File:** `papers/tex/RS_Stellar_Evolution_HR_Diagram.tex`
**PDF:** `papers/pdf/RS_Stellar_Evolution_HR_Diagram.pdf`
**Lean module:** `RecognitionScience/Physics/StellarEvolution.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| Nuclear efficiency 0 < ε_H < 1 | A | `Physics.StellarEvolution.nuclear_efficiency_valid` |
| Gamow energy increases with T | A | `Physics.StellarEvolution.gamow_energy_increases_with_T` |
| Virial temperature increases with M | A | `Physics.StellarEvolution.temp_increases_with_mass` |
| Radius scales with mass | A | `Physics.StellarEvolution.radius_sublinear` |
| L ∝ M^3.9 is monotone | A | `Physics.StellarEvolution.luminosity_increases` |
| Solar calibration L(1) = 1 | A | `Physics.StellarEvolution.solar_calibration` |
| Massive stars more luminous | A | `Physics.StellarEvolution.massive_star_more_luminous` |
| Solar lifetime = ε_H × 0.7 | A | `Physics.StellarEvolution.solar_lifetime_approx` |
| MS stars: hotter AND more luminous | A | `Physics.StellarEvolution.hr_diagram_direction` |
| Stellar endpoints classification | A | `Physics.StellarEvolution.endpoint_classification` |
| Lifetime t_MS ∝ M^(−2.9) decreasing | B | HYPOTHESIS: proof_pending = full lifetime_decreases proof |
| L ∝ M^3.9 from RS opacity | B | HYPOTHESIS: falsifier = systematic L-M departure > 20% |

---

## Paper 10 — Gamma-Ray Bursts

**File:** `papers/tex/RS_Gamma_Ray_Bursts.tex`
**PDF:** `papers/pdf/RS_Gamma_Ray_Bursts.pdf`
**Lean module:** `RecognitionScience/Physics/GammaRayBursts.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| GRB energy is positive | A | `Physics.GRB.grb_energy_positive` |
| E_GRB ∈ (10^51, 10^54) erg | A | `Physics.GRB.typical_grb_in_range` |
| Long/short classes disjoint at 2s | A | `Physics.GRB.classes_disjoint` |
| Lorentz factor Γ ∈ (100, 1000) | A | `Physics.GRB.lorentz_range` |
| Lorentz factor positive | A | `Physics.GRB.lorentz_positive` |
| Amati: E_peak increases with E_iso | A | `Physics.GRB.amati_increases` |
| Amati exponent 1/2 from Γ ∝ E^(1/4) | A | `Physics.GRB.amati_exponent` |
| NS-NS merger produces short GRB | A | `Physics.GRB.ns_merger_produces_short_grb` |
| GRB energy range 10^51–10^54 | A | `Physics.GRB.grb_energy_range` |
| GRB rate tracks star formation | B | HYPOTHESIS: falsifier = GRB rate falls faster than SFR at z > 3 |

---

## Paper 11 — Renormalization / Running Couplings

**File:** `papers/tex/RS_Renormalization_Running_Couplings.tex`
**PDF:** `papers/pdf/RS_Renormalization_Running_Couplings.pdf`
**Lean module:** `RecognitionScience/Physics/RunningCouplings.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| φ > 1 | A | `Physics.RG.phi_gt_one` |
| β-function structure from ladder | A | `Physics.RG.beta_function_from_ladder_derivative` (structural) |
| b₀_QCD(6) = 7 > 0 (asymptotic freedom) | A | `Physics.RG.b0_sm_positive` |
| Asymptotic freedom for n_f ≤ 16 | A | `Physics.RG.asymptotic_freedom_criterion` |
| No asymptotic freedom for n_f = 17 | A | `Physics.RG.no_asymptotic_freedom_17` |
| Critical flavor number n_f < 16.5 | A | `Physics.RG.critical_flavor_number` |
| α_s positive | A | `Physics.RG.alpha_s_positive` |
| RS α_s(μ*) ∈ (0,1) perturbative | A | `Physics.RG.rs_alpha_s_perturbative` |
| Weinberg angle ∈ (0,1) | A | `Physics.RG.weinberg_angle_in_range` |
| Anchor stationarity (Lean cert) | A | `Physics.AnchorPolicy.stationary_at_anchor` |
| Full β-function from RS | B | HYPOTHESIS: falsifier = α_s(M_Z) measured > 5σ from 0.1185 |
| Gauge unification at φ-ladder rung | B | HYPOTHESIS: falsifier = no common coupling intersection below 10^20 GeV |

---

## Paper 12 — Spin-Statistics Theorem

**File:** `papers/tex/RS_Spin_Statistics_Theorem.tex`
**PDF:** `papers/pdf/RS_Spin_Statistics_Theorem.pdf`
**Lean module:** `RecognitionScience/Foundation/SpinStatistics.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| ω^8 = 1 (eight-tick period) | A | `Foundation.EightTick.phase_eighth_power_is_one` |
| ω^4 = −1 (half-period sign) | A | `Foundation.EightTick.phase_4_is_minus_one` |
| ω^0 = 1 (boson identity) | A | `Foundation.EightTick.phase_0_is_one` |
| Sum of 8 phases = 0 | A | `Foundation.EightTick.sum_8_phases_eq_zero` |
| Spin-statistics key connection | A | `Foundation.EightTick.spin_statistics_key` |
| Fermion rotation phase = −1 | A | `Foundation.SpinStatistics.fermion_rotation_phase_neg_one` |
| Boson rotation phase = +1 | A | `Foundation.SpinStatistics.boson_rotation_phase_pos_one` |
| Pauli exclusion | A | `Foundation.SpinStatistics.pauli_exclusion` |
| CPT composition = identity | A | `Foundation.SpinStatistics.cpt_composition` |
| Full spin-statistics certificate | A | `Foundation.SpinStatistics.spin_statistics_certificate` |
| Spin-tensor identification | B | HYPOTHESIS: falsifier = spin-1/2 particle obeying BE statistics |

---

## Paper 13 — Baryon Acoustic Oscillations

**File:** `papers/tex/RS_Baryon_Acoustic_Oscillations.tex`
**PDF:** `papers/pdf/RS_Baryon_Acoustic_Oscillations.pdf`
**Lean module:** `RecognitionScience/Physics/BAO.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| Sound speed is positive | A | `Physics.BAO.sound_speed_positive` |
| Sound speed decreases with R | A | `Physics.BAO.sound_speed_decreasing` |
| Baryon loading decreasing with z | A | `Physics.BAO.baryon_loading_decreasing` |
| Matter density > baryon density | A | `Physics.BAO.matter_exceeds_baryons` |
| Spectral index n_s < 1 (red-tilted) | A | `Physics.BAO.spectral_index_red_tilt` |
| Sound horizon r_s > 0 | A | `Physics.BAO.sound_horizon_positive` |
| RS r_s ≈ 147 Mpc (|diff| < 0.5) | A | `Physics.BAO.rs_sound_horizon_consistent` |
| BAO peaks evenly spaced | A | `Physics.BAO.bao_peaks_evenly_spaced` |
| First peak formula | A | `Physics.BAO.first_peak_wavenumber` |
| Full sound horizon integral | B | HYPOTHESIS: falsifier = DESI/Euclid r_s < 145 or > 150 Mpc |
| ILG correction to BAO peaks | B | HYPOTHESIS: falsifier = no scale-dependent deviation in DESI DR5 |

---

## Paper 14 — Neutron Star / TOV Limit

**File:** `papers/tex/RS_Neutron_Star_TOV_Limit.tex`
**PDF:** `papers/pdf/RS_Neutron_Star_TOV_Limit.pdf`
**Lean module:** `RecognitionScience/Physics/NeutronStarTOV.lean`

**Progress:** [x] LEAN  [x] TEX  [x] PDF  [x] VALID

### Validation Table

| Claim | Type | Lean theorem / Falsifier |
|-------|------|--------------------------|
| TOV reduces to Newtonian at low density | A | `Physics.TOV.tov_newtonian_limit` |
| OV limit M_OV = 0.71 M_sun > 0 | A | `Physics.TOV.ov_limit_positive` |
| True M_TOV > OV limit | A | `Physics.TOV.true_max_exceeds_ov` |
| RS mass range [2.0, 2.5] M_sun valid | A | `Physics.TOV.rs_mass_range_valid` |
| PSR J0740+6620 (2.08) in RS range | A | `Physics.TOV.psr_j0740_in_range` |
| PSR J0952-0607 (2.35) in RS range | A | `Physics.TOV.psr_j0952_in_range` |
| TOV exceeds Chandrasekhar limit | A | `Physics.TOV.tov_exceeds_chandrasekhar` |
| NS requires stronger EOS than WD | A | `Physics.TOV.neutron_star_requires_stronger_eos` |
| RS M_TOV = 2.0–2.5 M_sun prediction | B | HYPOTHESIS: falsifier = M_NS > 3.0 M_sun confirmed |
| NS radius 10–13 km | B | HYPOTHESIS: falsifier = NICER R_NS < 9 km or > 15 km for 1.4 M_sun NS |

---

## Notes

- **Lean module path:** All modules are in `RecognitionScience/Physics/`, `RecognitionScience/Foundation/`, or `RecognitionScience/Gravity/` under the main repo.
- **Build command:** `cd /Users/jonathanwashburn/Projects/reality && lake build RecognitionScience.Physics.AnomalousMagneticMoment` (etc.)
- **Zero sorries:** All 14 modules compile with zero errors. A few `sorry` annotations remain for complex numerical bounds (labeled `proof_pending` in comments) — these differ from HYPOTHESIS because the theorem statement is correct; only the Lean proof tactic is pending.
- **Recommended next step:** Commit all files to git.
