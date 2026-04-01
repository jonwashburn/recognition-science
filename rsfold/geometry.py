"""PDB I/O, coordinate initialization, Kabsch RMSD."""

from typing import Optional, Tuple
import urllib.request

import numpy as np

from .constants import BACKBONE_DIST


def init_extended_chain(n: int, seed: int = 42) -> np.ndarray:
    """Initialize an extended chain of n CA atoms along the x-axis."""
    rng = np.random.RandomState(seed)
    coords = np.zeros((n, 3))
    for i in range(n):
        coords[i] = [i * BACKBONE_DIST, 0.0, 0.0]
    coords += rng.randn(n, 3) * 0.1
    return coords


def kabsch_rmsd(P: np.ndarray, Q: np.ndarray) -> float:
    """RMSD after optimal superposition (Kabsch algorithm)."""
    assert P.shape == Q.shape
    Pc = P - P.mean(axis=0)
    Qc = Q - Q.mean(axis=0)
    H = Pc.T @ Qc
    U, _S, Vt = np.linalg.svd(H)
    d = np.sign(np.linalg.det(Vt.T @ U.T))
    R = Vt.T @ np.diag([1.0, 1.0, d]) @ U.T
    P_rot = Pc @ R
    return float(np.sqrt(np.mean(np.sum((P_rot - Qc) ** 2, axis=1))))


def coords_to_pdb(coords: np.ndarray, sequence: str, path: str) -> None:
    """Write CA-only PDB file."""
    aa_1to3 = {
        "A": "ALA", "C": "CYS", "D": "ASP", "E": "GLU", "F": "PHE",
        "G": "GLY", "H": "HIS", "I": "ILE", "K": "LYS", "L": "LEU",
        "M": "MET", "N": "ASN", "P": "PRO", "Q": "GLN", "R": "ARG",
        "S": "SER", "T": "THR", "V": "VAL", "W": "TRP", "Y": "TYR",
    }
    with open(path, "w") as f:
        f.write("REMARK   RS-Fold predicted structure\n")
        f.write(f"REMARK   Sequence: {sequence}\n")
        for i, (x, y, z) in enumerate(coords):
            aa3 = aa_1to3.get(sequence[i] if i < len(sequence) else "G", "GLY")
            f.write(
                f"ATOM  {i+1:5d}  CA  {aa3} A{i+1:4d}    "
                f"{x:8.3f}{y:8.3f}{z:8.3f}  1.00  0.00           C\n"
            )
        f.write("END\n")


def download_pdb(pdb_id: str) -> Optional[Tuple[np.ndarray, str]]:
    """Download CA coordinates and sequence from RCSB PDB."""
    url = f"https://files.rcsb.org/download/{pdb_id}.pdb"
    aa_3to1 = {
        "ALA": "A", "CYS": "C", "ASP": "D", "GLU": "E", "PHE": "F",
        "GLY": "G", "HIS": "H", "ILE": "I", "LYS": "K", "LEU": "L",
        "MET": "M", "ASN": "N", "PRO": "P", "GLN": "Q", "ARG": "R",
        "SER": "S", "THR": "T", "VAL": "V", "TRP": "W", "TYR": "Y",
    }
    try:
        with urllib.request.urlopen(url, timeout=15) as resp:
            pdb_text = resp.read().decode("utf-8")
        coords, sequence = [], []
        seen: set[str] = set()
        for line in pdb_text.split("\n"):
            if line.startswith("ATOM") and line[12:16].strip() == "CA":
                res_id = f"{line[21]}_{line[22:27].strip()}"
                if res_id not in seen:
                    seen.add(res_id)
                    coords.append([float(line[30:38]), float(line[38:46]), float(line[46:54])])
                    sequence.append(aa_3to1.get(line[17:20].strip(), "G"))
        if coords:
            return np.array(coords), "".join(sequence)
    except Exception:
        pass
    return None
