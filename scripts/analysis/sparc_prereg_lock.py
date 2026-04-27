#!/usr/bin/env python3
"""Freeze the prereg systematics-flag list and parameter lock as JSON."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUTPUT_PATH = ROOT / "artifacts/sparc_prereg_systematics_lock.json"
PREREG_DOC = ROOT / "papers/RS_PhiLocked_SPARC_Prereg.md"
VERIFIER = ROOT / "scripts/analysis/gravity_paper_v07_sparc_verify.py"
SYSTEMATICS_HELPER = ROOT / "scripts/analysis/mass_to_light_sparc_systematics_p0yr.py"
SPARC_TABLE = ROOT / "external/gravity/legacy/archives/snapshot-20250816-182339-tree/history/SPARC_Lelli2016c.mrt.txt"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    alpha_lock = (1.0 - 1.0 / phi) / 2.0
    locked = {
        "title": "RS_PhiLocked_SPARC_Prereg",
        "git_tag_target": "prereg/sparc-2026-04-26",
        "prereg_doc": str(PREREG_DOC.relative_to(ROOT)),
        "verifier_script": str(VERIFIER.relative_to(ROOT)),
        "verifier_sha256": sha256_file(VERIFIER),
        "systematics_helper_script": str(SYSTEMATICS_HELPER.relative_to(ROOT)),
        "systematics_helper_sha256": sha256_file(SYSTEMATICS_HELPER),
        "sparc_catalog_path": str(SPARC_TABLE.relative_to(ROOT)),
        "sparc_catalog_sha256": sha256_file(SPARC_TABLE),
        "phi": phi,
        "alpha_lock": alpha_lock,
        "model_constants": {
            "Upsilon_star": phi,
            "alpha": 1.0 - 1.0 / phi,
            "C_xi": 2.0 * phi ** (-4),
            "A": 1.0 + alpha_lock / 2.0,
            "p": 1.0 - alpha_lock / 4.0,
            "N_tau_galactic": 142.4,
            "N_r_galactic": 126.3,
            "tau0_seconds_seam_path": "data/calibration_tau0_seconds_gravity.json",
        },
        "error_model": {
            "sigma0_kms": 10.0,
            "f_floor": 0.05,
            "alpha_beam": 0.30,
            "sigma_asym_dwarf": 0.10,
            "sigma_asym_spiral": 0.05,
            "k_turb": 0.07,
            "p_turb": 1.30,
            "outer_disk_dvdr_threshold_kms_per_kpc": -5.0,
            "outer_disk_start_factor_Rd": 2.0,
        },
        "mask_rules": {
            "inner_cut_rad_over_Rd": 0.30,
            "snr_cut_vobs_over_verr": 3.0,
            "outer_disk_cut": "exclude points with r >= 2 R_d and dv/dr < -5 km/s/kpc, applied at the first such point onward",
        },
        "vmax_classification": {
            "dwarf_below_kms": 80.0,
            "spiral_max_kms": 200.0,
        },
        "decision_rule": {
            "pass_mean_chi2N": 2.0,
            "pass_fraction_passed": 0.7,
            "fail_mean_chi2N": 2.0,
            "fail_fraction_passed_below": 0.5,
            "f_good_threshold_chi2N": 2.0,
        },
        "falsifiers": {
            "F1_full_Q1_median_chi2N_above": 5.0,
            "F2_Q2_strictly_worse_than_Q1_with_mean_above": 4.0,
            "F3_BTFR_slope_band": [3.5, 4.5],
            "F4_per_galaxy_parameter_used_anywhere": "any per-galaxy fit voids the prereg",
        },
        "systematics_flags": {
            "policy": "n_flags(g) >= 3 implies high_risk; otherwise low_risk",
            "flag_definitions": [
                {
                    "id": "inclination_high_ge_75",
                    "expression": "catalog Inc_deg >= 75",
                },
                {
                    "id": "inclination_low_le_35",
                    "expression": "catalog Inc_deg <= 35",
                },
                {
                    "id": "distance_flag_nonzero",
                    "expression": "catalog f_D != 0",
                },
                {
                    "id": "bulge_proxy_max_vbul_over_vdisk_ge_0p25",
                    "expression": "max|vbul|/max|vdisk| >= 0.25 from rotmod",
                },
                {
                    "id": "bulge_proxy_max_vbul_over_vobs_ge_0p15",
                    "expression": "max|vbul|/max|vobs| >= 0.15 from rotmod",
                },
                {
                    "id": "vflat_missing_or_zero",
                    "expression": "catalog Vflat_kms <= 0 or non-finite",
                },
                {
                    "id": "outer_extent_lt_4_Rd",
                    "expression": "max(rad)/R_d < 4 from rotmod and catalog",
                },
                {
                    "id": "flat_velocity_decline_vflat_over_vmax_lt_0p9",
                    "expression": "catalog Vflat / max(vobs) < 0.9 (only if Vflat finite and >0)",
                },
                {
                    "id": "gas_fraction_lt_0p15",
                    "expression": "f_gas = 1.33 MHI / (Upsilon_star L36 + 1.33 MHI) < 0.15",
                },
            ],
            "high_risk_threshold_n_flags": 3,
        },
        "samples": {
            "discovery_Q": 1,
            "holdout_Q": [2, 3],
            "external_planned": ["LITTLE_THINGS", "wide_binaries_Hernandez_2024"],
        },
        "comparator": {
            "name": "MOND_simple_mu",
            "a0_si": 1.23e-10,
            "tuning": "fixed, not refit per galaxy or per sample",
        },
        "outputs_planned": [
            "artifacts/gravity_paper_v07_sparc_phi_locked.json",
            "artifacts/sparc_phi_locked_q2_holdout.json",
            "artifacts/sparc_phi_locked_q3_holdout.json",
            "artifacts/sparc_phi_locked_q1_random_half.json",
            "artifacts/sparc_phi_locked_btfr_locked.json",
            "artifacts/sparc_prereg_systematics_lock.json (this file)",
        ],
        "notes": [
            "All hashes computed at write time over the source files.",
            "Any change to the verifier or systematics helper after the prereg invalidates the prereg.",
            "Re-running prereg lock requires a new git tag and a new prereg note.",
        ],
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(locked, indent=2, sort_keys=True) + "\n")
    print(json.dumps(locked, indent=2, sort_keys=True))
    print(f"\nWrote: {OUTPUT_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
