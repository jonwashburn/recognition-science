"""Tryptamine Phi-Ladder Calculator.

Maps tryptamine molecules to phi-ladder rungs and computes the coupling/control
balance for each analog. Predicts excursion depth from molecular structure.

Lean refs:
  - DMTPhiLadder: dmtCouplingMultiplier = phi, dmtControlFactor = 1/phi
  - OptimalAnalogDesign: balanced_coupling = phi^(half_rung/2),
                         balanced_control = phi^(-half_rung/2)
  - DMTStateTransition: dmtEffectiveRank(dose) = 3 * (1 + dose)
"""

import math
from dataclasses import dataclass
from typing import List, Dict

from . import PHI


SEROTONIN_MW: float = 176.21
DMT_MW: float = 188.27

KNOWN_TRYPTAMINES: Dict[str, float] = {
    "DMT":       188.27,
    "5-MeO-DMT": 218.30,
    "4-HO-DMT":  204.27,   # psilocin
    "psilocybin": 284.25,
    "bufotenin":  204.27,
    "DET":        216.32,
    "DPT":        244.38,
    "5-MeO-MiPT": 246.35,
    "serotonin":  176.21,
    "melatonin":  232.28,
    "tryptamine": 160.22,
}


def j_cost(r: float) -> float:
    """J(r) = (r + 1/r)/2 - 1. The unique RS cost function."""
    if r <= 0:
        return 1000.0
    return 0.5 * (r + 1.0 / r) - 1.0


@dataclass
class AnalogProfile:
    name: str
    molecular_weight: float
    serotonin_ratio: float
    j_cost_vs_serotonin: float
    half_rung: int
    coupling: float
    control: float
    balance: float
    effective_rank_at_dose_1: float
    predicted_depth: str


def compute_half_rung(mw: float) -> int:
    """Find the nearest phi-ladder half-rung for a given molecular weight.
    half_rung = round(2 * log_phi(MW / serotonin_MW))"""
    ratio = mw / SEROTONIN_MW
    if ratio <= 0:
        return 0
    log_phi = math.log(ratio) / math.log(PHI)
    return round(2.0 * log_phi)


def balanced_coupling(half_rung: int) -> float:
    """Lean ref: OptimalAnalogDesign.balanced_coupling = phi^(half_rung/2)"""
    return PHI ** (half_rung / 2.0)


def balanced_control(half_rung: int) -> float:
    """Lean ref: OptimalAnalogDesign.balanced_control = phi^(-half_rung/2)"""
    return PHI ** (-half_rung / 2.0)


def effective_rank(dose: float) -> float:
    """Lean ref: DMTStateTransition.dmtEffectiveRank = 3 * (1 + dose)"""
    return 3.0 * (1.0 + dose)


def depth_label(rank: float) -> str:
    if rank < 4:
        return "sub-threshold"
    if rank < 6:
        return "light"
    if rank < 8:
        return "moderate (bypasses meditation)"
    if rank < 15:
        return "deep (approaches dissolution)"
    return "breakthrough"


def analyze_molecule(name: str, mw: float) -> AnalogProfile:
    """Compute the full phi-ladder profile for a tryptamine."""
    ratio = mw / SEROTONIN_MW
    hr = compute_half_rung(mw)
    coup = balanced_coupling(hr)
    ctrl = balanced_control(hr)
    eff_rank = effective_rank(1.0)
    return AnalogProfile(
        name=name,
        molecular_weight=mw,
        serotonin_ratio=ratio,
        j_cost_vs_serotonin=j_cost(ratio),
        half_rung=hr,
        coupling=coup,
        control=ctrl,
        balance=coup * ctrl,
        effective_rank_at_dose_1=eff_rank,
        predicted_depth=depth_label(eff_rank),
    )


def analyze_all_known() -> List[AnalogProfile]:
    """Analyze all known tryptamines in the library."""
    return [analyze_molecule(name, mw) for name, mw in sorted(KNOWN_TRYPTAMINES.items())]


def design_analog(target_half_rung: int) -> Dict[str, float]:
    """Design a tryptamine analog for a specific phi-ladder rung.
    Returns the target molecular weight, coupling, and control."""
    target_mw = SEROTONIN_MW * (PHI ** (target_half_rung / 2.0))
    return {
        "half_rung": target_half_rung,
        "target_mw": target_mw,
        "coupling": balanced_coupling(target_half_rung),
        "control": balanced_control(target_half_rung),
        "balance": 1.0,
        "depth_at_dose_1": depth_label(effective_rank(1.0)),
    }
