"""DFT-8 WToken extraction (matches Lean ProteinFolding/Encoding/WToken.lean).

Pipeline: sequence chemistry -> per-residue DFT-8 spectra -> WTokens (mode, phi-level, phase).
"""

from dataclasses import dataclass
from typing import List, Tuple

import numpy as np

from .constants import PHI
from .chemistry import AAChemistry


@dataclass
class WToken:
    dominant_mode: int   # 0..7
    phi_level: int       # 0..3
    phase: int           # 0..7


def spectra_per_residue(signal: List[float]) -> List[np.ndarray]:
    """Centered 8-window DFT per residue (zero-padded at boundaries).
    Compatible with Lean's 8-tick alignment."""
    n = len(signal)
    spectra: List[np.ndarray] = []
    for i in range(n):
        window = []
        for off in range(-3, 5):
            idx = i + off
            window.append(signal[idx] if 0 <= idx < n else 0.0)
        spectra.append(np.fft.fft(np.array(window, dtype=float)))
    return spectra


def quantize_phi_level(amplitude: float) -> int:
    """Matches WToken.quantizePhiLevel."""
    if amplitude < 1.0 / (PHI ** 2):
        return 0
    if amplitude < 1.0 / PHI:
        return 1
    if amplitude < 1.0:
        return 2
    return 3


def quantize_phase(theta: float) -> int:
    """Matches WToken.quantizePhase ([-pi, pi] -> {0..7})."""
    normalized = (theta + np.pi) / (2.0 * np.pi)
    return int(np.floor(normalized * 8)) % 8


def find_dominant_mode(X: np.ndarray) -> int:
    """Matches Lean findDominantMode: prefer among modes {2,4,1,3}, excluding DC."""
    amps = np.abs(X)
    a2, a4, a1, a3 = amps[2], amps[4], amps[1], amps[3]
    if a2 >= a4 and a2 >= a1 and a2 >= a3:
        return 2
    if a4 >= a1 and a4 >= a3:
        return 4
    if a1 >= a3:
        return 1
    return 3


def extract_wtokens(spectra: List[np.ndarray]) -> List[WToken]:
    """Extract a WToken from each per-residue spectrum."""
    tokens: List[WToken] = []
    for X in spectra:
        k = find_dominant_mode(X)
        amp = float(np.abs(X[k]))
        ph = float(np.angle(X[k]))
        tokens.append(WToken(k, quantize_phi_level(amp), quantize_phase(ph)))
    return tokens


def strand_signal_D11(X: np.ndarray, chem: AAChemistry) -> float:
    """Matches Derivations/D11_StrandDetection.lean strandSignal formula."""
    p4 = float(np.abs(X[4]) ** 2)
    p2 = float(np.abs(X[2]) ** 2)
    alternation = np.sqrt(p4 / 8.0)
    helix_sig = np.sqrt(p2 / 8.0)
    rigidity = 1.0 - chem.flexibility
    branch = 0.2 if (0.25 < chem.volume < 0.45 and chem.flexibility < 0.5 and chem.charge == 0.0) else 0.0
    arom = 0.15 if chem.aromaticity > 0.5 else 0.0
    return PHI * alternation + rigidity + branch + arom - helix_sig


def detect_strand_runs_from_tokens(
    tokens: List[WToken], min_len: int = 3
) -> List[Tuple[int, int]]:
    """Detect beta-strand runs from WTokens (mode=4, phi_level>=1)."""
    positions = [i for i, t in enumerate(tokens) if t.dominant_mode == 4 and t.phi_level >= 1]
    if not positions:
        return []
    runs: List[Tuple[int, int]] = []
    start = prev = positions[0]
    for idx in positions[1:]:
        if idx == prev + 1:
            prev = idx
        else:
            if prev - start + 1 >= min_len:
                runs.append((start, prev + 1))
            start = prev = idx
    if prev - start + 1 >= min_len:
        runs.append((start, prev + 1))
    return runs
