#!/usr/bin/env python3
"""LITTLE THINGS dwarf-irregular ingestion stub.

Drop the public LITTLE THINGS catalog at the path printed by `--check`,
then this script will normalise it into the SPARC-shaped fields expected
by `scripts/analysis/sparc_phi_locked_holdout.py`. Until the data lands,
the script only verifies the planned destination paths and writes a
status artifact so the prereg policy is auditable.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET_CATALOG = ROOT / "external/gravity/legacy/archives/little_things/little_things_catalog.csv"
TARGET_ROTMOD = ROOT / "external/gravity/legacy/archives/little_things/Rotmod_LITTLE_THINGS"
OUTPUT = ROOT / "artifacts/sparc_phi_locked_little_things_ingest_status.json"
PREREG = ROOT / "papers/RS_PhiLocked_LITTLE_THINGS_Prereg.md"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="report ingest status and exit")
    args = ap.parse_args()

    catalog_present = TARGET_CATALOG.exists()
    rotmod_present = TARGET_ROTMOD.exists() and any(TARGET_ROTMOD.glob("*_rotmod.dat"))

    status = {
        "row": "P0-YR LITTLE THINGS",
        "prereg_doc": str(PREREG.relative_to(ROOT)),
        "catalog_path_planned": str(TARGET_CATALOG.relative_to(ROOT)),
        "rotmod_dir_planned": str(TARGET_ROTMOD.relative_to(ROOT)),
        "catalog_present": bool(catalog_present),
        "rotmod_present": bool(rotmod_present),
        "ready_to_run": bool(catalog_present and rotmod_present),
        "ingest_step_required": (
            "Download the public LITTLE THINGS rotation curves and Iorio et al. 2017 "
            "decomposition products, normalise them into SPARC-shaped columns "
            "(rad, vobs, verr, vgas, vdisk, vbul, sbdisk, sbbul), and place under "
            "external/gravity/legacy/archives/little_things/."
        ),
        "next_actions": [
            "place catalog and rotmod files at the planned paths",
            "rerun this script without --check to record SHA256 of every file",
            "extend scripts/analysis/sparc_phi_locked_holdout.py with --mode little_things",
            "produce artifacts/sparc_phi_locked_little_things_holdout.json",
            "add IndisputableMonolith/Gravity/MassToLightLITTLE_THINGSHoldoutScoreCard.lean",
        ],
        "falsifier": (
            "If LITTLE THINGS dwarf high-chi2 fraction exceeds the SPARC dwarf "
            "high-chi2 fraction by more than 10 percentage points under the locked "
            "policy, the dwarf-friendliness prediction of phi-locked ILG is refuted."
        ),
    }

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))
    print(f"\nWrote: {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
