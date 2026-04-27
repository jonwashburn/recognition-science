#!/usr/bin/env python3
"""Phase B: locked-policy hold-out runner for SPARC Q=2, Q=3, and Q=1 random halves.

Imports the v07 verifier internals so that the model, masks, error model, and
gas-fraction quintile thresholds (computed once from Q=1) are guaranteed
identical to the discovery sample. No per-galaxy fitting.

Outputs JSON artifacts referenced by the prereg.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
from dataclasses import asdict
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
VERIFIER = ROOT / "scripts/analysis/gravity_paper_v07_sparc_verify.py"
SYSTEMATICS_HELPER = ROOT / "scripts/analysis/mass_to_light_sparc_systematics_p0yr.py"
ROTMOD_DIR = ROOT / "external/gravity/active/data/Rotmod_LTG"
TAU0_SEAM = ROOT / "data/calibration_tau0_seconds_gravity.json"


def load_module(path: Path, name: str):
    import sys

    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot import {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_glob(base: Path, pattern: str) -> dict[str, Any]:
    files = sorted(p for p in base.glob(pattern) if p.is_file())
    digest = hashlib.sha256()
    for p in files:
        rel = str(p.relative_to(ROOT))
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(sha256_file(p).encode("utf-8"))
        digest.update(b"\0")
    return {
        "glob_base": str(base.relative_to(ROOT)),
        "glob": pattern,
        "file_count": len(files),
        "combined_sha256": digest.hexdigest(),
    }


def chi2_metrics(rows: list[dict[str, Any]]) -> dict[str, Any]:
    chi = np.array([float(g["chi2N_cr"]) for g in rows], dtype=float)
    mond = np.array([float(g["chi2N_mond"]) for g in rows], dtype=float)
    if chi.size == 0:
        return {
            "N": 0,
            "median_chi2N_causal_response": None,
            "mean_chi2N_causal_response": None,
            "fraction_causal_response_passed": None,
            "median_chi2N_mond": None,
            "mean_chi2N_mond": None,
            "outliers_chi2N_gt_5_causal_response": 0,
            "outliers_chi2N_gt_5_mond": 0,
        }
    return {
        "N": int(chi.size),
        "median_chi2N_causal_response": float(np.median(chi)),
        "mean_chi2N_causal_response": float(np.mean(chi)),
        "fraction_causal_response_passed": float(np.mean(chi < 2.0)),
        "median_chi2N_mond": float(np.median(mond)),
        "mean_chi2N_mond": float(np.mean(mond)),
        "outliers_chi2N_gt_5_causal_response": int(np.sum(chi > 5.0)),
        "outliers_chi2N_gt_5_mond": int(np.sum(mond > 5.0)),
    }


def decision(metrics: dict[str, Any]) -> dict[str, str]:
    mean_v = metrics.get("mean_chi2N_causal_response")
    fgood = metrics.get("fraction_causal_response_passed")
    if mean_v is None or fgood is None:
        return {"result": "ERROR", "reason": "no rows"}
    if mean_v < 2.0 and fgood > 0.7:
        return {"result": "PASS", "reason": f"mean={mean_v:.3f}<2.0 and f_good={fgood:.3f}>0.7"}
    if mean_v > 2.0 or fgood < 0.5:
        return {"result": "FAIL", "reason": f"mean={mean_v:.3f}, f_good={fgood:.3f}"}
    return {"result": "INCONCLUSIVE", "reason": f"mean={mean_v:.3f}, f_good={fgood:.3f}"}


def run_q_subset(verifier, sysmod, params, meta, q_set: set[int],
                 seed: int | None = None,
                 random_half_label: str | None = None) -> dict[str, Any]:
    sparc = verifier.parse_sparc_table1_mrt(verifier.find_sparc_mrt(ROOT))
    sparc = sparc.copy()
    sparc["f_gas"] = [
        verifier.gas_fraction_from_catalog(L36, MHI, params.upsilon_star)
        for L36, MHI in zip(sparc["L36_1e9Lsun"], sparc["MHI_1e9Msun"])
    ]
    q1 = sparc[sparc["Q"] == 1]
    fvals = q1["f_gas"].to_numpy(dtype=float)
    fvals = fvals[np.isfinite(fvals)]
    thresholds = (
        np.quantile(fvals, [0.2, 0.4, 0.6, 0.8])
        if fvals.size
        else np.array([0.2, 0.4, 0.6, 0.8])
    )

    target = sparc[sparc["Q"].isin(q_set)].copy()
    if random_half_label is not None:
        rng = np.random.default_rng(seed if seed is not None else 0)
        names = sorted(target["Galaxy"].astype(str).tolist())
        rng.shuffle(names)
        if random_half_label == "A":
            keep = set(names[: len(names) // 2])
        elif random_half_label == "B":
            keep = set(names[len(names) // 2:])
        else:
            raise ValueError("random_half_label must be 'A' or 'B'")
        target = target[target["Galaxy"].astype(str).isin(keep)].copy()

    catalog_meta = sysmod.parse_catalog(sysmod.SPARC_TABLE)

    per_galaxy: list[dict[str, Any]] = []
    for row in target.itertuples(index=False):
        name = str(row.Galaxy)
        rot_path = ROTMOD_DIR / f"{name}_rotmod.dat"
        if not rot_path.exists():
            continue
        df_rot = verifier.load_rotmod(rot_path)
        if df_rot.empty:
            continue
        r_kpc = df_rot["rad"].to_numpy(dtype=float)
        vobs = df_rot["vobs"].to_numpy(dtype=float)
        verr = df_rot["verr"].to_numpy(dtype=float)
        vmax = float(np.max(vobs)) if vobs.size else float("nan")

        Rd = float(row.Rdisk_kpc) if np.isfinite(row.Rdisk_kpc) and row.Rdisk_kpc > 0 else float("nan")
        if not np.isfinite(Rd) or Rd <= 0:
            vdisk = df_rot["vdisk"].to_numpy(dtype=float)
            if np.any(vdisk > 0):
                Rd = float(r_kpc[int(np.argmax(vdisk))] / 2.2)
            else:
                Rd = 2.0

        u_b = verifier.u_b_from_quintiles(float(row.f_gas), thresholds)
        xi = verifier.xi_from_u_b(u_b, params.C_xi)
        if not np.isfinite(xi):
            xi = 1.0

        vbar = verifier.baryon_velocity_kms(df_rot, params.upsilon_star)
        w = verifier.weight_w(r_kpc, vbar, df_rot, Rd, xi, params=params)
        v_model = np.sqrt(np.maximum(w, 0.0)) * vbar

        b_kpc = 0.3 * Rd
        mask = r_kpc >= b_kpc
        mask &= (vobs / verr) >= 3.0
        r_cut = verifier.find_outer_cut_r_kpc(r_kpc, vobs, Rd)
        if r_cut is not None:
            mask &= r_kpc <= r_cut
        if mask.sum() < 1:
            continue

        gtype = verifier.galaxy_type_from_vmax(vmax)
        sigma_asym = verifier.SIGMA_ASYM_DWARF if gtype == "dwarf" else verifier.SIGMA_ASYM_SPIRAL
        sig = verifier.sigma_eff_kms(r_kpc, vobs, verr, Rd, sigma_asym)
        res = (vobs - v_model)[mask]
        sig_m = sig[mask]
        chi2 = float(np.sum((res / sig_m) ** 2))
        chi2N = float(chi2 / mask.sum())

        a_bar = verifier.acceleration_si(vbar, r_kpc)
        a_mond = verifier.mond_simple_accel(np.maximum(a_bar, 1e-30), a0=1.23e-10)
        v_mond = np.sqrt(np.maximum(a_mond, 0.0) * (r_kpc * verifier.KPC_TO_M)) / verifier.KM_TO_M
        res_m = (vobs - v_mond)[mask]
        chi2_m = float(np.sum((res_m / sig_m) ** 2))
        chi2N_m = float(chi2_m / mask.sum())

        per_galaxy.append({
            "name": name,
            "Q": int(row.Q),
            "vmax_kms": vmax,
            "vflat_kms": float(row.Vflat_kms) if np.isfinite(row.Vflat_kms) else 0.0,
            "n_points": int(mask.sum()),
            "chi2N_cr": chi2N,
            "chi2N_mond": chi2N_m,
        })

    # Apply locked systematics flags using the same helper as the discovery sample.
    annotated: list[dict[str, Any]] = []
    for g in per_galaxy:
        meta_row = catalog_meta.get(g["name"])
        if meta_row is None:
            g["n_systematics_flags"] = None
            g["systematics_flags"] = None
            annotated.append(g)
            continue
        try:
            audit = sysmod.summarize_galaxy(g, meta_row)
            g["n_systematics_flags"] = int(audit["n_flags"])
            g["systematics_flags"] = audit["flags"]
        except Exception as e:  # missing rotmod cols, etc.
            g["n_systematics_flags"] = None
            g["systematics_flags"] = None
            g["systematics_error"] = str(e)
        annotated.append(g)

    full = chi2_metrics(annotated)
    low_risk = chi2_metrics([g for g in annotated if g.get("n_systematics_flags") is not None
                             and int(g["n_systematics_flags"]) < 3])
    high_risk = chi2_metrics([g for g in annotated if g.get("n_systematics_flags") is not None
                              and int(g["n_systematics_flags"]) >= 3])

    return {
        "per_galaxy": annotated,
        "full_metrics": full,
        "low_risk_metrics": low_risk,
        "high_risk_metrics": high_risk,
        "decision_full": decision(full),
        "decision_low_risk": decision(low_risk),
        "decision_high_risk": decision(high_risk),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["q2", "q3", "q1_random_half", "q1q2_combined", "q1q2q3_combined", "q2q3_combined"], required=True)
    ap.add_argument("--seed", type=int, default=20260426)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    verifier = load_module(VERIFIER, "v07_verifier")
    sysmod = load_module(SYSTEMATICS_HELPER, "sparc_sys")
    params, meta = verifier.rs_params_v07(
        ROOT,
        tau0_seam_path=TAU0_SEAM.relative_to(ROOT),
        N_tau=142.4,
        N_r=126.3,
        upsilon_policy="phi",
        upsilon_star=None,
    )

    artifact: dict[str, Any] = {
        "mode": args.mode,
        "seed": int(args.seed),
        "model_constants": {
            "Upsilon_star": params.upsilon_star,
            "alpha": params.alpha,
            "C_xi": params.C_xi,
            "A": params.A,
            "p": params.p,
            "r0_kpc": params.r0_kpc,
            "a0_si": params.a0_si,
        },
        "inputs": {
            "verifier_script": str(VERIFIER.relative_to(ROOT)),
            "verifier_sha256": sha256_file(VERIFIER),
            "systematics_helper": str(SYSTEMATICS_HELPER.relative_to(ROOT)),
            "systematics_helper_sha256": sha256_file(SYSTEMATICS_HELPER),
            "rotmod_glob": sha256_glob(ROTMOD_DIR, "*_rotmod.dat"),
            "sparc_catalog_sha256": sha256_file(verifier.find_sparc_mrt(ROOT)),
        },
        "prereg_doc": "papers/RS_PhiLocked_SPARC_Prereg.md",
        "prereg_lock_artifact": "artifacts/sparc_prereg_systematics_lock.json",
    }

    if args.mode == "q2":
        result = run_q_subset(verifier, sysmod, params, meta, q_set={2})
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q2_holdout.json"
    elif args.mode == "q3":
        result = run_q_subset(verifier, sysmod, params, meta, q_set={3})
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q3_holdout.json"
    elif args.mode == "q1q2_combined":
        result = run_q_subset(verifier, sysmod, params, meta, q_set={1, 2})
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q1q2_combined.json"
    elif args.mode == "q1q2q3_combined":
        result = run_q_subset(verifier, sysmod, params, meta, q_set={1, 2, 3})
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q1q2q3_combined.json"
    elif args.mode == "q2q3_combined":
        result = run_q_subset(verifier, sysmod, params, meta, q_set={2, 3})
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q2q3_combined.json"
    else:
        a = run_q_subset(verifier, sysmod, params, meta, q_set={1},
                         seed=args.seed, random_half_label="A")
        b = run_q_subset(verifier, sysmod, params, meta, q_set={1},
                         seed=args.seed, random_half_label="B")
        result = {
            "half_A": a,
            "half_B": b,
            "decision_half_A_full": a["decision_full"],
            "decision_half_B_full": b["decision_full"],
        }
        out = args.out or ROOT / "artifacts/sparc_phi_locked_q1_random_half.json"

    artifact["result"] = result
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in artifact.items() if k != "result"}, indent=2, sort_keys=True))
    if args.mode in {"q2", "q3", "q1q2_combined", "q1q2q3_combined", "q2q3_combined"}:
        print("\n=== full ===")
        print(json.dumps(result["full_metrics"], indent=2, sort_keys=True))
        print(json.dumps(result["decision_full"], indent=2, sort_keys=True))
        print("\n=== low risk ===")
        print(json.dumps(result["low_risk_metrics"], indent=2, sort_keys=True))
        print(json.dumps(result["decision_low_risk"], indent=2, sort_keys=True))
        print("\n=== high risk ===")
        print(json.dumps(result["high_risk_metrics"], indent=2, sort_keys=True))
        print(json.dumps(result["decision_high_risk"], indent=2, sort_keys=True))
    else:
        print("\n=== half A ===")
        print(json.dumps(result["half_A"]["full_metrics"], indent=2, sort_keys=True))
        print(json.dumps(result["half_A"]["decision_full"], indent=2, sort_keys=True))
        print("\n=== half B ===")
        print(json.dumps(result["half_B"]["full_metrics"], indent=2, sort_keys=True))
        print(json.dumps(result["half_B"]["decision_full"], indent=2, sort_keys=True))
    print(f"\nWrote: {out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
