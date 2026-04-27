#!/usr/bin/env python3
"""Wide-binary ingestion stub (Hernandez 2024 / El-Badry 2021).

Mirrors the LITTLE THINGS stub: until real data lands, this only writes
a status artifact so the prereg policy is auditable.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET_CATALOG = ROOT / "external/gravity/legacy/archives/wide_binaries/wide_binaries_catalog.csv"
OUTPUT = ROOT / "artifacts/sparc_phi_locked_wide_binaries_ingest_status.json"
PREREG = ROOT / "papers/RS_PhiLocked_WideBinaries_Prereg.md"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.parse_args()

    catalog_present = TARGET_CATALOG.exists()
    status = {
        "row": "P0-YR wide_binaries",
        "prereg_doc": str(PREREG.relative_to(ROOT)),
        "catalog_path_planned": str(TARGET_CATALOG.relative_to(ROOT)),
        "catalog_present": bool(catalog_present),
        "ready_to_run": bool(catalog_present),
        "ingest_step_required": (
            "Download the Hernandez 2024 wide-binary catalog and El-Badry 2021 Gaia EDR3 "
            "wide-binary table, normalise into columns (pair_id, separation_kau, "
            "v_relative_kms, e_v_relative_kms, total_mass_Msun, parallax_mas, source), "
            "and place at the planned path."
        ),
        "next_actions": [
            "place wide_binaries_catalog.csv at the planned path",
            "rerun this script without --check to record SHA256 + row count",
            "add scripts/analysis/sparc_phi_locked_wide_binaries.py with the locked policy",
            "produce artifacts/sparc_phi_locked_wide_binaries.json",
            "add IndisputableMonolith/Gravity/MassToLightWideBinariesScoreCard.lean",
        ],
        "falsifier": (
            "If v_RMS in the outermost three bins is consistent with pure Newtonian "
            "(no enhancement) at >3sigma, OR exceeds ILG at >3sigma, the wide-binary "
            "row is refuted."
        ),
    }

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))
    print(f"\nWrote: {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
