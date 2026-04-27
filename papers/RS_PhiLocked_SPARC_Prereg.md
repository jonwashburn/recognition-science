# RS_PhiLocked_SPARC_Prereg

**Title:** A φ-Locked Information-Limited Gravity Test on SPARC: Preregistered, Zero Per-Galaxy Parameters
**Author:** Jonathan Washburn, Recognition Physics Institute
**Created:** 2026-04-26
**Status:** preregistration, locked at git tag `prereg/sparc-2026-04-26`
**Companion artifacts:**
- `artifacts/gravity_paper_v07_sparc_phi_locked.json` (Q=1, the only sample seen so far)
- `artifacts/sparc_prereg_systematics_lock.json` (the seven fixed flags, locked)
- All Lean modules under `IndisputableMonolith/Gravity/MassToLightSPARC*ScoreCard.lean`

This file freezes the model, the sample policy, the mask rules, the error model, the systematics flags, the decision rule, and the falsifier **before** the Q=2 and Q=3 hold-out replications run. Anyone reading this after the git tag has full audit access to verify nothing was altered after the prereg.

## 1. Theory layer

Information-Limited Gravity (ILG) is the discrete-resolution correction to GR forced by the φ-lattice ledger. The Lean derivation is `IndisputableMonolith/Gravity/ILGFromLedger.lean` and the rotation-curve hook is `IndisputableMonolith/Gravity/MassToLightScoreCard.lean`.

Locked structural constants (all derived from φ, no fitting):

- `Υ★ = φ`, with `1.61 < Υ★ < 1.62`. Lean: `MassToLightScoreCard.row_upsilon_star_eq_phi`.
- `α_lock = (1 − 1/φ) / 2 ≈ 0.191`.
- `α = 1 − 1/φ` (the dynamical-time exponent used in the v07 verifier).
- `C_ξ = 2 φ⁻⁴`.
- `A = 1 + α_lock / 2`.
- `p = 1 − α_lock / 4`.
- Galactic ladder rungs: `N_τ = 142.4`, `N_r = 126.3`.
- `r0_kpc` and `a0_si` are computed from those rungs given the gravity-domain seam `data/calibration_tau0_seconds_gravity.json`.
- Per-galaxy free parameters: `0`. Lean: `SPARCFalsifier.zero_free_params`.

The error-model hyperparameters are global, declared, not derived:

- `σ0 = 10.0 km/s`
- `f_floor = 0.05`
- `α_beam = 0.30`
- `σ_asym_dwarf = 0.10`
- `σ_asym_spiral = 0.05`
- `K_turb = 0.07`
- `p_turb = 1.30`
- Outer-disk cut threshold: `dv/dr < −5 km/s/kpc` beyond `2 R_d`.

Source of truth: `scripts/analysis/gravity_paper_v07_sparc_verify.py` at the tagged commit. The Python file is itself part of the prereg and must not be edited after the tag without versioning the prereg.

## 2. Sample policy

The discovery sample is **SPARC Q=1** at the local snapshot `external/gravity/legacy/archives/snapshot-20250816-182339-tree/history/SPARC_Lelli2016c.mrt.txt`, with rotation curves in `external/gravity/active/data/Rotmod_LTG/*_rotmod.dat`. After applying the global mask rules (Section 4) the discovery sample is `N_disc = 99`.

Hold-out samples are **SPARC Q=2** (`N ≈ 64` before mask rules) and **SPARC Q=3** (`N ≈ 12`). Hold-outs run separately and report results separately. No Q=2 or Q=3 numbers may modify the locked policy.

The discovery sample's gas-fraction quintile thresholds (used only for the global `ξ` weighting) are computed once over Q=1 and reused unchanged for Q=2, Q=3, and any future external sample.

## 3. Galaxy classification

Kinematic classification by `vmax` (the per-galaxy maximum of `vobs`):

- `dwarf`: `vmax < 80 km/s`
- `spiral`: `80 ≤ vmax ≤ 200 km/s`
- `massive`: `vmax > 200 km/s`

The classification is a fixed function and is not used to alter the model.

## 4. Mask rules

For every galaxy:

1. Inner cut: `r ≥ 0.3 R_d`, where `R_d` is from the SPARC catalog's `Rdisk_kpc`. If `Rdisk_kpc` is missing or non-positive, fall back to `R_d = r_at_argmax(vdisk) / 2.2` per the verifier.
2. SNR cut: `vobs / verr ≥ 3`.
3. Outer-disk cut: exclude points beyond the first radius `r ≥ 2 R_d` at which `dv/dr < −5 km/s/kpc`.

These are the v07 paper masks. They are global, not per-galaxy.

## 5. Error model

The effective error on each masked point is

```
σ²_eff = verr² + σ0² + (f_floor · vobs)² + σ_beam² + σ_asym² + σ_turb²
σ_beam  = α_beam · (b · vobs) / (r + b),    b = 0.3 R_d
σ_asym  = σ_asym_dwarf if dwarf else σ_asym_spiral
σ_turb  = K_turb · vobs · (1 − exp(−r / R_d))^p_turb
```

with the constants from Section 1. These are global and apply uniformly to ILG and the MOND baseline.

## 6. Decision rule

For each Q-subset (Q=1 discovery, Q=2 hold-out, Q=3 hold-out):

- `PASS` iff `mean χ²/N < 2.0` AND `f_good > 0.7` over the Q subset, after masks.
- `FAIL` iff `mean χ²/N > 2.0` OR `f_good < 0.5`.
- Otherwise `INCONCLUSIVE`.

`f_good` is the fraction of galaxies in the Q-subset with `χ²/N < 2.0`.

The discovery sample has already been seen and produces `mean = 2.898`, `f_good = 0.626`, `INCONCLUSIVE` under this rule. The discovery sample's median is `1.516`, which passes both `< 3.0` and `< 5.0`.

## 7. Falsifier

ILG is falsified if any of the following holds with the locked parameters and masks:

- F1: `median χ²/N > 5.0` on the **full** Q=1 sample (discovery falsifier).
- F2: `mean χ²/N` on Q=2 strictly worse than on Q=1 with `mean > 4.0`.
- F3: BTFR slope from Q=1 (paper-defined `Vflat`, mean of last three masked points) outside `(3.5, 4.5)`.
- F4: an analysis after the prereg shows a per-galaxy fit was used in any locked output.

The falsifiers are deliberately simple. We do not adjudicate inconclusive outcomes by additional cuts.

## 8. Preregistered systematics flags

Before any hold-out run, the seven flags below are locked. They use only the SPARC catalog metadata and the rotmod columns. They are not used to repair, mask, or remove any data point in the discovery analysis. They are reported alongside the result, and a secondary policy (Section 9) is preregistered separately.

For each galaxy:

1. `inclination_high_ge_75`: `Inc_deg ≥ 75°`.
2. `inclination_low_le_35`: `Inc_deg ≤ 35°`.
3. `distance_flag_nonzero`: `f_D ≠ 0`.
4. `bulge_proxy_max_vbul_over_vdisk_ge_0p25`: `max|vbul| / max|vdisk| ≥ 0.25`.
5. `bulge_proxy_max_vbul_over_vobs_ge_0p15`: `max|vbul| / max|vobs| ≥ 0.15`.
6. `vflat_missing_or_zero`: catalog `Vflat_kms ≤ 0` or non-finite.
7. `outer_extent_lt_4_Rd`: `max(rad) / R_d < 4`.
8. `flat_velocity_decline_vflat_over_vmax_lt_0p9`: catalog `Vflat / vmax < 0.9`.
9. `gas_fraction_lt_0p15`: phi-locked `f_gas < 0.15`, where `f_gas = 1.33 MHI / (Υ★ L36 + 1.33 MHI)`.

The first listing rule of "seven flags" in earlier audit text was loose; the locked, prereg version is the nine flags above. The frozen JSON in `artifacts/sparc_prereg_systematics_lock.json` is the canonical list.

## 9. Secondary preregistered policy

The fixed-flag policy is preregistered for both reporting and for a secondary pass:

- `n_flags(g)`: count of locked flags (Section 8) tripped by galaxy `g`.
- `low_risk(g)`: `n_flags(g) < 3`.
- `high_risk(g)`: `n_flags(g) ≥ 3`.
- For each Q-subset (Q=1, Q=2, Q=3) we report the decision rule (Section 6) on three samples: full, low-risk, and high-risk.

The discovery-sample numbers under this policy were obtained post-hoc on Q=1; they do not count as a prereg pass. The Q=2 and Q=3 hold-out numbers under the same policy do count.

## 10. Comparator

The MOND simple-μ baseline with `a0 = 1.23 × 10⁻¹⁰ m/s²` is run with the same masks, error model, and reporting. The paper reports both ILG and MOND on the same samples. We do not tune `a0`.

## 11. Outputs and artifact path

The hold-out runs write JSON to:

- `artifacts/sparc_phi_locked_q2_holdout.json`
- `artifacts/sparc_phi_locked_q3_holdout.json`
- `artifacts/sparc_phi_locked_q1_random_half.json`
- `artifacts/sparc_phi_locked_btfr_locked.json`

Each artifact records `mean_chi2N_causal_response`, `median_chi2N_causal_response`, `fraction_causal_response_passed`, the matching MOND values, dataset counts, the locked systematics counts, and a SHA256 of the catalog and rotmod glob.

All values feed Lean scorecards under `IndisputableMonolith/Gravity/MassToLightSPARC*Holdout*ScoreCard.lean` and `IndisputableMonolith/Gravity/MassToLightBTFRSlopeScoreCard.lean`.

## 12. Decision tree summary

| Sample | Decision rule | Outcome (locked at prereg time) |
|---|---|---|
| Q=1 discovery | mean<2.0 ∧ f_good>0.7 | INCONCLUSIVE (mean=2.898, f_good=0.626) |
| Q=1 median falsifier | median<5.0 | PASS (median=1.516) |
| Q=1 tight target | median<3.0 | PASS (median=1.516) |
| Q=1 random half A | reported only | TBD at run time |
| Q=1 random half B | reported only | TBD at run time |
| Q=2 hold-out | mean<2.0 ∧ f_good>0.7 | TBD at run time |
| Q=3 hold-out | mean<2.0 ∧ f_good>0.7 | TBD at run time |
| Low-risk subsets | mean<2.0 ∧ f_good>0.7 | TBD at run time |
| BTFR slope | β ∈ (3.5, 4.5) | TBD at run time |

If both Q=2 hold-out and BTFR slope are PASS under the locked rules, the row P0-YR moves from `MIXED` to `PARTIAL_THEOREM + EMPIRICAL PASS`. Otherwise, the row stays `MIXED` and the paper reports the negative result.
