#!/usr/bin/env python3
"""
rs_genomics — Zero-Parameter Amino Acid Substitution Geometry
=============================================================

Derives a geometric distance between any two amino acids using:
  1. DFT-8 WToken vectors (Fubini-Study distance on CP^6)
  2. J-cost of molecular weight and hydrophobicity ratios

Zero fitted parameters. Zero training data.
All constants derived from the 8-tick cycle and J(x) = (x + 1/x)/2 - 1.

Usage as a library:
    >>> from rs_genomics import score, score_all, AMINO_ACIDS
    >>> score("E", "V")          # Glu -> Val (sickle cell mutation)
    2.6613...
    >>> score_all()              # full 20x20 matrix

Usage from the command line:
    python rs_genomics.py score --ref E --alt V
    python rs_genomics.py matrix
    python rs_genomics.py matrix --format csv
    python rs_genomics.py benchmark --clinvar data/clinvar_10k_sample.csv

Reference:
    Washburn et al., "The Genetic Code Architecture is Forced by a Single
    Functional Equation" (2026).
    Lean 4 proofs: IndisputableMonolith.Water.WTokenIso,
                   IndisputableMonolith.Genetics.JCostWithinFamily

Repository: https://github.com/jonwashburn/recognition-science
License: MIT
"""

__version__ = "1.0.0"

import argparse
import csv
import json
import math
import sys
from io import StringIO

# ---------------------------------------------------------------------------
# Amino acid data (all from first principles or standard biochemistry tables)
# ---------------------------------------------------------------------------

AMINO_ACIDS_3 = [
    "Gly", "Ala", "Val", "Leu", "Ile", "Pro", "Phe", "Trp",
    "Met", "Ser", "Thr", "Cys", "Tyr", "His", "Asp", "Glu",
    "Asn", "Gln", "Lys", "Arg",
]

_3TO1 = {
    "Gly": "G", "Ala": "A", "Val": "V", "Leu": "L", "Ile": "I",
    "Pro": "P", "Phe": "F", "Trp": "W", "Met": "M", "Ser": "S",
    "Thr": "T", "Cys": "C", "Tyr": "Y", "His": "H", "Asp": "D",
    "Glu": "E", "Asn": "N", "Gln": "Q", "Lys": "K", "Arg": "R",
}
_1TO3 = {v: k for k, v in _3TO1.items()}

AMINO_ACIDS = list(_3TO1.values())  # single-letter codes

_AA_IDX = {aa: i for i, aa in enumerate(AMINO_ACIDS_3)}

FULL_NAMES = {
    "G": "Glycine", "A": "Alanine", "V": "Valine", "L": "Leucine",
    "I": "Isoleucine", "P": "Proline", "F": "Phenylalanine",
    "W": "Tryptophan", "M": "Methionine", "S": "Serine",
    "T": "Threonine", "C": "Cysteine", "Y": "Tyrosine",
    "H": "Histidine", "D": "Aspartic acid", "E": "Glutamic acid",
    "N": "Asparagine", "Q": "Glutamine", "K": "Lysine", "R": "Arginine",
}

FAMILIES = {
    "F17": ["Gly", "Ala", "Val", "Leu"],
    "F26": ["Ser", "Thr", "Asn", "Gln"],
    "F35": ["Asp", "Glu", "Lys", "Arg"],
    "F4":  ["His", "Phe", "Tyr", "Trp", "Pro", "Cys", "Met", "Ile"],
}

FAMILY_LABELS = {
    "F17": "Small nonpolar",
    "F26": "Polar uncharged",
    "F35": "Charged",
    "F4":  "Aromatic / cyclic / sulfur",
}

_AA_TO_FAMILY = {}
for _fam, _members in FAMILIES.items():
    for _aa in _members:
        _AA_TO_FAMILY[_aa] = _fam

MW = {
    "Gly": 75, "Ala": 89, "Val": 117, "Leu": 131, "Ile": 131,
    "Pro": 115, "Phe": 165, "Trp": 204, "Met": 149, "Ser": 105,
    "Thr": 119, "Cys": 121, "Tyr": 181, "His": 155, "Asp": 133,
    "Glu": 147, "Asn": 132, "Gln": 146, "Lys": 146, "Arg": 174,
}

HYDROPHOBICITY = {
    "Gly": -4, "Ala": 18, "Val": 42, "Leu": 38, "Ile": 45,
    "Pro": -16, "Phe": 28, "Trp": -9, "Met": 19, "Ser": -8,
    "Thr": -7, "Cys": 25, "Tyr": -13, "His": -32, "Asp": -35,
    "Glu": -35, "Asn": -35, "Gln": -35, "Lys": -39, "Arg": -45,
}

# Grantham (1974) — the industry-standard 3-parameter empirical baseline
_GRANTHAM_RAW = {
    ("A","R"):112,("A","N"):111,("A","D"):126,("A","C"):195,("A","Q"):91,
    ("A","E"):107,("A","G"):60,("A","H"):86,("A","I"):94,("A","L"):96,
    ("A","K"):106,("A","M"):84,("A","F"):113,("A","P"):27,("A","S"):99,
    ("A","T"):58,("A","W"):148,("A","Y"):112,("A","V"):64,
    ("R","N"):86,("R","D"):96,("R","C"):180,("R","Q"):43,("R","E"):54,
    ("R","G"):125,("R","H"):29,("R","I"):97,("R","L"):102,("R","K"):26,
    ("R","M"):91,("R","F"):97,("R","P"):103,("R","S"):110,("R","T"):71,
    ("R","W"):101,("R","Y"):77,("R","V"):96,
    ("N","D"):23,("N","C"):139,("N","Q"):46,("N","E"):42,("N","G"):80,
    ("N","H"):68,("N","I"):149,("N","L"):153,("N","K"):94,("N","M"):142,
    ("N","F"):158,("N","P"):91,("N","S"):46,("N","T"):65,("N","W"):174,
    ("N","Y"):143,("N","V"):133,
    ("D","C"):154,("D","Q"):61,("D","E"):45,("D","G"):94,("D","H"):81,
    ("D","I"):168,("D","L"):172,("D","K"):101,("D","M"):160,("D","F"):177,
    ("D","P"):108,("D","S"):65,("D","T"):85,("D","W"):181,("D","Y"):160,
    ("D","V"):152,
    ("C","Q"):154,("C","E"):170,("C","G"):159,("C","H"):174,("C","I"):198,
    ("C","L"):198,("C","K"):202,("C","M"):196,("C","F"):205,("C","P"):169,
    ("C","S"):112,("C","T"):149,("C","W"):215,("C","Y"):194,("C","V"):192,
    ("Q","E"):29,("Q","G"):87,("Q","H"):24,("Q","I"):109,("Q","L"):113,
    ("Q","K"):53,("Q","M"):101,("Q","F"):116,("Q","P"):76,("Q","S"):68,
    ("Q","T"):42,("Q","W"):130,("Q","Y"):99,("Q","V"):96,
    ("E","G"):98,("E","H"):40,("E","I"):134,("E","L"):138,("E","K"):56,
    ("E","M"):126,("E","F"):140,("E","P"):93,("E","S"):80,("E","T"):65,
    ("E","W"):152,("E","Y"):122,("E","V"):121,
    ("G","H"):98,("G","I"):135,("G","L"):138,("G","K"):127,("G","M"):127,
    ("G","F"):153,("G","P"):42,("G","S"):56,("G","T"):59,("G","W"):184,
    ("G","Y"):147,("G","V"):109,
    ("H","I"):94,("H","L"):99,("H","K"):32,("H","M"):87,("H","F"):100,
    ("H","P"):77,("H","S"):89,("H","T"):47,("H","W"):115,("H","Y"):83,
    ("H","V"):84,
    ("I","L"):5,("I","K"):102,("I","M"):10,("I","F"):21,("I","P"):95,
    ("I","S"):142,("I","T"):89,("I","W"):61,("I","Y"):33,("I","V"):29,
    ("L","K"):107,("L","M"):15,("L","F"):22,("L","P"):98,("L","S"):145,
    ("L","T"):92,("L","W"):61,("L","Y"):36,("L","V"):32,
    ("K","M"):95,("K","F"):102,("K","P"):103,("K","S"):121,("K","T"):78,
    ("K","W"):110,("K","Y"):85,("K","V"):97,
    ("M","F"):28,("M","P"):87,("M","S"):135,("M","T"):81,("M","W"):67,
    ("M","Y"):36,("M","V"):21,
    ("F","P"):114,("F","S"):155,("F","T"):103,("F","W"):40,("F","Y"):22,
    ("F","V"):50,
    ("P","S"):74,("P","T"):38,("P","W"):147,("P","Y"):110,("P","V"):68,
    ("S","T"):58,("S","W"):177,("S","Y"):144,("S","V"):124,
    ("T","W"):128,("T","Y"):92,("T","V"):69,
    ("W","Y"):37,("W","V"):88,
    ("Y","V"):55,
}

_GRANTHAM = {}
for (_a, _b), _d in _GRANTHAM_RAW.items():
    _GRANTHAM[(_a, _b)] = _d
    _GRANTHAM[(_b, _a)] = _d

# WToken assignment table (from Lean: WTokenIso.lean)
_WTOKEN_ASSIGNMENT = [
    (1, True,  0, 0, "Gly"), (1, True,  1, 0, "Ala"),
    (1, True,  2, 0, "Val"), (1, True,  3, 0, "Leu"),
    (2, True,  0, 0, "Ser"), (2, True,  1, 0, "Thr"),
    (2, True,  2, 0, "Asn"), (2, True,  3, 0, "Gln"),
    (3, True,  0, 0, "Asp"), (3, True,  1, 0, "Glu"),
    (3, True,  2, 0, "Lys"), (3, True,  3, 0, "Arg"),
    (4, False, 0, 0, "His"), (4, False, 1, 0, "Phe"),
    (4, False, 2, 0, "Tyr"), (4, False, 3, 0, "Trp"),
    (4, False, 0, 2, "Pro"), (4, False, 1, 2, "Cys"),
    (4, False, 2, 2, "Met"), (4, False, 3, 2, "Ile"),
]

# ---------------------------------------------------------------------------
# Core mathematics (pure Python — no numpy required for scoring)
# ---------------------------------------------------------------------------

def jcost(x):
    """J(x) = (x + 1/x) / 2 - 1.  The unique canonical reciprocal cost."""
    if x <= 0:
        return float("inf")
    return (x + 1.0 / x) / 2.0 - 1.0


def _resolve(code):
    """Accept 1-letter or 3-letter code, return 3-letter."""
    if len(code) == 1:
        code = code.upper()
        if code not in _1TO3:
            raise ValueError(f"Unknown amino acid code: {code}")
        return _1TO3[code]
    code = code.capitalize()
    if code not in _AA_IDX:
        raise ValueError(f"Unknown amino acid code: {code}")
    return code


# ---------------------------------------------------------------------------
# DFT-8 vector construction (requires numpy, but only called once lazily)
# ---------------------------------------------------------------------------

_VECTORS = None
_D_FS = None
_D_PRODUCT = None


def _ensure_vectors():
    """Lazily build the WToken vectors and distance matrices on first use."""
    global _VECTORS, _D_FS, _D_PRODUCT
    if _VECTORS is not None:
        return

    import numpy as np

    def omega8():
        return np.exp(-1j * np.pi / 4.0)

    def dft8_mode(k):
        w = omega8()
        return np.array([w ** (t * k) / np.sqrt(8.0) for t in range(8)],
                        dtype=np.complex128)

    vectors = {}
    for mode_k, is_pair, phi_level, tau_offset, aa_name in _WTOKEN_ASSIGNMENT:
        if is_pair:
            base = dft8_mode(mode_k) + dft8_mode((8 - mode_k) % 8)
        else:
            base = dft8_mode(mode_k)

        if phi_level > 0:
            base = np.roll(base, phi_level)

        if mode_k == 4 and tau_offset == 2:
            base = 1j * base

        base = base / np.linalg.norm(base)
        vectors[aa_name] = base

    n = len(AMINO_ACIDS_3)
    D_fs = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            inner = min(abs(np.vdot(vectors[AMINO_ACIDS_3[i]],
                                     vectors[AMINO_ACIDS_3[j]])), 1.0)
            d = math.acos(inner)
            D_fs[i][j] = D_fs[j][i] = d

    D_prod = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            aa1, aa2 = AMINO_ACIDS_3[i], AMINO_ACIDS_3[j]
            fs = D_fs[i][j]
            mw1, mw2 = MW[aa1], MW[aa2]
            h1, h2 = HYDROPHOBICITY[aa1] + 50, HYDROPHOBICITY[aa2] + 50
            j_mw = jcost(mw1 / mw2) if mw1 != mw2 else 0.0
            j_h = jcost(h1 / h2) if h1 != h2 else 0.0
            d = math.sqrt(fs ** 2 + j_mw ** 2 + j_h ** 2)
            D_prod[i][j] = D_prod[j][i] = d

    _VECTORS = vectors
    _D_FS = D_fs
    _D_PRODUCT = D_prod


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def score(ref, alt):
    """Return the RS geometric substitution distance between two amino acids.

    Parameters
    ----------
    ref : str
        Reference amino acid (1-letter or 3-letter code).
    alt : str
        Alternate amino acid (1-letter or 3-letter code).

    Returns
    -------
    float
        The RS 2D product metric distance (zero fitted parameters).
    """
    _ensure_vectors()
    r3, a3 = _resolve(ref), _resolve(alt)
    return _D_PRODUCT[_AA_IDX[r3]][_AA_IDX[a3]]


def grantham(ref, alt):
    """Return the Grantham (1974) distance between two amino acids."""
    r1 = _3TO1[_resolve(ref)]
    a1 = _3TO1[_resolve(alt)]
    if r1 == a1:
        return 0.0
    return float(_GRANTHAM.get((r1, a1), 0.0))


def info(code):
    """Return a dict of metadata for a single amino acid."""
    aa3 = _resolve(code)
    aa1 = _3TO1[aa3]
    fam = _AA_TO_FAMILY[aa3]
    return {
        "code1": aa1,
        "code3": aa3,
        "name": FULL_NAMES[aa1],
        "family": fam,
        "family_label": FAMILY_LABELS[fam],
        "mw": MW[aa3],
        "hydrophobicity": HYDROPHOBICITY[aa3],
    }


def score_pair(ref, alt):
    """Return a detailed result dict for one substitution."""
    _ensure_vectors()
    r3, a3 = _resolve(ref), _resolve(alt)
    ri, ai = _AA_IDX[r3], _AA_IDX[a3]
    rs_dist = _D_PRODUCT[ri][ai]
    fs_dist = _D_FS[ri][ai]
    g_dist = grantham(ref, alt)
    r_fam = _AA_TO_FAMILY[r3]
    a_fam = _AA_TO_FAMILY[a3]
    return {
        "ref": info(ref),
        "alt": info(alt),
        "rs_distance": rs_dist,
        "fubini_study": fs_dist,
        "grantham": g_dist,
        "crosses_families": r_fam != a_fam,
        "family_transition": f"{r_fam} -> {a_fam}",
    }


def score_all():
    """Return the full 20x20 RS distance matrix as a list of lists."""
    _ensure_vectors()
    return [row[:] for row in _D_PRODUCT]


def grantham_all():
    """Return the full 20x20 Grantham distance matrix as a list of lists."""
    n = len(AMINO_ACIDS_3)
    G = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            aa1, aa2 = _3TO1[AMINO_ACIDS_3[i]], _3TO1[AMINO_ACIDS_3[j]]
            d = _GRANTHAM.get((aa1, aa2), 0.0)
            G[i][j] = G[j][i] = d
    return G


def benchmark_clinvar(csv_path):
    """Run the RS scorer against a ClinVar CSV and return AUC-ROC.

    The CSV must have columns: ref, alt, classification
    where classification is 'pathogenic' or 'benign'.
    """
    _ensure_vectors()

    path_scores, ben_scores = [], []
    n_skipped = 0
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                d = score(row["ref"], row["alt"])
            except (ValueError, KeyError):
                n_skipped += 1
                continue
            if row["classification"].strip().lower() == "pathogenic":
                path_scores.append(d)
            else:
                ben_scores.append(d)

    n_path, n_ben = len(path_scores), len(ben_scores)
    if n_path == 0 or n_ben == 0:
        return {"error": "No pathogenic or benign variants found."}

    count = 0
    for p in path_scores:
        for b in ben_scores:
            if p > b:
                count += 1
            elif p == b:
                count += 0.5
    auc = count / (n_path * n_ben)

    return {
        "n_pathogenic": n_path,
        "n_benign": n_ben,
        "n_skipped": n_skipped,
        "mean_rs_pathogenic": sum(path_scores) / n_path,
        "mean_rs_benign": sum(ben_scores) / n_ben,
        "auc_roc": auc,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _cli_score(args):
    result = score_pair(args.ref, args.alt)
    print(f"  {result['ref']['code1']} ({result['ref']['name']})  ->  "
          f"{result['alt']['code1']} ({result['alt']['name']})")
    print(f"  RS distance:     {result['rs_distance']:.4f}")
    print(f"  Fubini-Study:    {result['fubini_study']:.4f}")
    print(f"  Grantham:        {result['grantham']:.0f}")
    print(f"  Crosses family:  {result['crosses_families']}  "
          f"({result['family_transition']})")


def _cli_matrix(args):
    _ensure_vectors()
    mat = score_all()
    n = len(AMINO_ACIDS_3)
    codes = [_3TO1[aa] for aa in AMINO_ACIDS_3]

    if args.format == "csv":
        buf = StringIO()
        w = csv.writer(buf)
        w.writerow([""] + codes)
        for i in range(n):
            w.writerow([codes[i]] + [f"{mat[i][j]:.4f}" for j in range(n)])
        print(buf.getvalue(), end="")
    elif args.format == "json":
        print(json.dumps({
            "amino_acids": codes,
            "matrix": mat,
            "metric": "RS 2D product (DFT-8 + J-cost)",
            "fitted_parameters": 0,
        }, indent=2))
    else:
        header = "    " + "  ".join(f"{c:>6s}" for c in codes)
        print(header)
        for i in range(n):
            row = f" {codes[i]}  " + "  ".join(
                f"{mat[i][j]:6.3f}" for j in range(n))
            print(row)


def _cli_benchmark(args):
    print(f"Running RS scorer on {args.clinvar} ...")
    result = benchmark_clinvar(args.clinvar)
    if "error" in result:
        print(f"  ERROR: {result['error']}")
        return
    print(f"  Pathogenic variants: {result['n_pathogenic']}")
    print(f"  Benign variants:     {result['n_benign']}")
    print(f"  Skipped:             {result['n_skipped']}")
    print(f"  Mean RS (pathogenic): {result['mean_rs_pathogenic']:.4f}")
    print(f"  Mean RS (benign):     {result['mean_rs_benign']:.4f}")
    print(f"  AUC-ROC:              {result['auc_roc']:.4f}")
    print(f"  Fitted parameters:    0")


def main():
    parser = argparse.ArgumentParser(
        prog="rs_genomics",
        description="RS Genomics — Zero-parameter amino acid substitution geometry",
    )
    sub = parser.add_subparsers(dest="command")

    p_score = sub.add_parser("score", help="Score a single substitution")
    p_score.add_argument("--ref", required=True, help="Reference AA (1 or 3 letter)")
    p_score.add_argument("--alt", required=True, help="Alternate AA (1 or 3 letter)")

    p_matrix = sub.add_parser("matrix", help="Print the full 20x20 distance matrix")
    p_matrix.add_argument("--format", choices=["table", "csv", "json"],
                          default="table", help="Output format")

    p_bench = sub.add_parser("benchmark", help="Benchmark against ClinVar data")
    p_bench.add_argument("--clinvar", required=True, help="Path to ClinVar CSV")

    args = parser.parse_args()

    if args.command == "score":
        _cli_score(args)
    elif args.command == "matrix":
        _cli_matrix(args)
    elif args.command == "benchmark":
        _cli_benchmark(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
