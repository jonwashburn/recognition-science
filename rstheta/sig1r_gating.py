"""Sigma-1 Receptor Gating and Neuroprotection Model.

Models the Sig-1R as a J-cost barrier modulator at the ER-mitochondria interface.
Computes theoretical cell survival extension during hypoxia/cardiac arrest.

Lean refs:
  - Sigma1ReceptorModel: CellularBoundary, effectiveBarrier, activationFromDose
  - DMTNeuroprotection: survivalWithDMT, neuroprotection_is_tether_maintenance
  - EndogenousDMTRelease: stressCost (hypoxia model)
  - DMTWaterCoherence: amplifiedClusterSize (hydration shell enhancement)
"""

import math
from dataclasses import dataclass
from typing import List

from . import PHI


def activation_from_dose(dose: float) -> float:
    """Sig-1R activation sigmoid: a = dose / (dose + 1).
    Lean ref: Sigma1ReceptorModel.activationFromDose"""
    if dose <= 0:
        return 0.0
    return dose / (dose + 1.0)


def effective_barrier(baseline_barrier: float, activation: float) -> float:
    """J-cost barrier after Sig-1R activation.
    Lean ref: Sigma1ReceptorModel.effectiveBarrier
    At full activation (a=1), barrier drops to zero."""
    return baseline_barrier * (1.0 - activation)


def survival_with_dmt(base_survival: float, activation: float) -> float:
    """Cell survival probability under DMT-mediated Sig-1R activation.
    Lean ref: DMTNeuroprotection.survivalWithDMT
    At full activation (a=1), survival = 1.0 (complete protection)."""
    return base_survival + activation * (1.0 - base_survival)


def amplified_cluster_size(base_n: int, activation: float) -> int:
    """Water coherence cluster size amplified by DMT.
    Lean ref: DMTWaterCoherence.amplifiedClusterSize"""
    return base_n + math.ceil(activation * base_n)


def hypoxia_stress(oxygen_fraction: float) -> float:
    """Metabolic stress from oxygen deprivation (0 = anoxia, 1 = normoxia).
    Lean ref: EndogenousDMTRelease.stressCost"""
    return 1.0 / (oxygen_fraction + 0.01)


def endogenous_release(stress: float) -> float:
    """Endogenous DMT release rate as function of stress.
    Lean ref: EndogenousDMTRelease.dmtReleaseRate"""
    if stress <= 0:
        return 0.0
    return stress / (stress + 1.0)


@dataclass
class NeuroprotectionResult:
    oxygen_fraction: float
    stress: float
    endogenous_dmt_release: float
    sig1r_activation: float
    barrier_reduction_pct: float
    survival_without_dmt: float
    survival_with_dmt: float
    survival_gain: float
    cluster_amplification: int
    clinical_interpretation: str


def model_cardiac_arrest(
    baseline_barrier: float = 5.0,
    baseline_survival: float = 0.3,
    base_cluster: int = 20,
    oxygen_trace: List[float] = None,
) -> List[NeuroprotectionResult]:
    """Model the neuroprotection cascade during cardiac arrest.

    Simulates the endogenous DMT release -> Sig-1R activation -> barrier
    reduction -> survival extension chain at decreasing oxygen levels.

    The oxygen_trace defaults to a 10-step ramp from normoxia to anoxia.
    """
    if oxygen_trace is None:
        oxygen_trace = [1.0, 0.8, 0.6, 0.4, 0.2, 0.1, 0.05, 0.02, 0.01, 0.0]

    results = []
    for o2 in oxygen_trace:
        stress = hypoxia_stress(o2)
        release = endogenous_release(stress)
        act = activation_from_dose(release)
        barrier = effective_barrier(baseline_barrier, act)
        surv_with = survival_with_dmt(baseline_survival, act)
        cluster = amplified_cluster_size(base_cluster, act)

        if o2 > 0.5:
            interp = "Normal perfusion. Minimal endogenous DMT."
        elif o2 > 0.1:
            interp = "Hypoxia. Endogenous DMT release increasing. Sig-1R activation rising."
        elif o2 > 0.01:
            interp = "Severe hypoxia. Near-maximal DMT release. Strong neuroprotection active."
        else:
            interp = "Cardiac arrest / anoxia. Maximum endogenous DMT. Full Sig-1R gating."

        results.append(NeuroprotectionResult(
            oxygen_fraction=o2,
            stress=stress,
            endogenous_dmt_release=release,
            sig1r_activation=act,
            barrier_reduction_pct=(1.0 - barrier / baseline_barrier) * 100 if baseline_barrier > 0 else 0,
            survival_without_dmt=baseline_survival,
            survival_with_dmt=surv_with,
            survival_gain=surv_with - baseline_survival,
            cluster_amplification=cluster,
            clinical_interpretation=interp,
        ))

    return results
