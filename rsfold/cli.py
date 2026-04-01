"""RS-Fold command-line interface."""

import argparse
import json
import sys
import time

import numpy as np

from . import __version__
from .fold import fold, BackboneFirstFolder
from .geometry import download_pdb, kabsch_rmsd, coords_to_pdb
from .energy import compute_rg


BENCHMARK_PROTEINS = [
    ("1L2Y", "NLYIQWLKDGGPSSGRPPPS", "Trp-cage"),
    ("1VII", None, "Villin headpiece HP36"),
    ("1ENH", None, "Engrailed homeodomain"),
    ("1PGB", None, "Protein G B1"),
    ("1T8J", None, "BBA5"),
]


def cmd_fold(args):
    seq = args.sequence
    if args.fasta:
        with open(args.fasta) as f:
            lines = [l.strip() for l in f if not l.startswith(">") and l.strip()]
            seq = "".join(lines)
    if not seq:
        print("Error: provide --sequence or --fasta", file=sys.stderr)
        sys.exit(1)

    print(f"RS-Fold v{__version__}")
    print(f"Sequence: {seq[:40]}{'...' if len(seq) > 40 else ''} ({len(seq)} residues)")
    print(f"Iterations: {args.iterations}")
    print()

    t0 = time.time()
    result = fold(seq, iterations=args.iterations, seed=args.seed, verbose=True)
    elapsed = time.time() - t0

    print(f"\nDone in {elapsed:.1f}s")
    print(f"Final energy: {result.energy:.1f}")
    print(f"Rg: {result.rg:.2f} A")
    print(f"Contacts predicted: {len(result.contacts)}")

    if args.output:
        coords_to_pdb(result.coords, seq, args.output)
        print(f"PDB written to {args.output}")

    if args.json:
        out = {
            "sequence": seq,
            "energy": result.energy,
            "rg": result.rg,
            "n_contacts": len(result.contacts),
            "elapsed_s": elapsed,
            "coords": result.coords.tolist(),
            "energy_trace": result.energy_trace,
        }
        with open(args.json, "w") as f:
            json.dump(out, f)
        print(f"JSON written to {args.json}")


def cmd_benchmark(args):
    print(f"RS-Fold Benchmark Suite v{__version__}")
    print("=" * 60)

    results = []
    for pdb_id, hardcoded_seq, name in BENCHMARK_PROTEINS:
        print(f"\n{pdb_id} - {name}")
        data = download_pdb(pdb_id)
        if data is None:
            print("  [SKIP] Could not download PDB")
            continue
        native_coords, pdb_seq = data
        seq = hardcoded_seq or pdb_seq
        native_rg = compute_rg(native_coords)
        print(f"  Sequence: {seq[:30]}... ({len(seq)} residues)")
        print(f"  Native Rg: {native_rg:.2f} A")

        t0 = time.time()
        result = fold(seq, iterations=args.iterations, seed=42, verbose=False)
        elapsed = time.time() - t0

        n = min(len(result.coords), len(native_coords))
        rmsd = kabsch_rmsd(result.coords[:n], native_coords[:n])
        rg_err = abs(result.rg - native_rg) / native_rg * 100.0

        print(f"  Predicted Rg: {result.rg:.2f} A (error {rg_err:.1f}%)")
        print(f"  RMSD: {rmsd:.2f} A")
        print(f"  Time: {elapsed:.1f}s")

        results.append({
            "pdb_id": pdb_id, "name": name,
            "n_residues": len(seq), "rmsd": rmsd,
            "rg_predicted": result.rg, "rg_native": native_rg,
            "rg_error_pct": rg_err, "energy": result.energy,
            "elapsed_s": elapsed,
        })

    if args.output:
        with open(args.output, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\nResults saved to {args.output}")


def main():
    parser = argparse.ArgumentParser(
        prog="rsfold",
        description="RS-Fold: Glass-box protein folding on the phi-lattice",
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    sub = parser.add_subparsers(dest="command")

    p_fold = sub.add_parser("fold", help="Fold a protein sequence")
    p_fold.add_argument("--sequence", "-s", type=str, default="")
    p_fold.add_argument("--fasta", "-f", type=str, default="")
    p_fold.add_argument("--output", "-o", type=str, default="")
    p_fold.add_argument("--json", type=str, default="")
    p_fold.add_argument("--iterations", "-n", type=int, default=2000)
    p_fold.add_argument("--seed", type=int, default=42)

    p_bench = sub.add_parser("benchmark", help="Run benchmark suite")
    p_bench.add_argument("--output", "-o", type=str, default="")
    p_bench.add_argument("--iterations", "-n", type=int, default=2000)

    args = parser.parse_args()
    if args.command == "fold":
        cmd_fold(args)
    elif args.command == "benchmark":
        cmd_benchmark(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
