"""Tether Mechanics: Phase Coupling, Safety, and Excursion Dynamics.

Computes the tether coupling strength, excursion fraction, decoherence time,
and safety bounds for tethered excursions (meditation, dreaming, DMT).

Lean refs:
  - DMTTetherMechanism: tetherStrength = sig1r_activation.activation_level,
    THEOREM_dmt_tether_safe (Z conserved, body survives, tether nonneg)
  - DMTNeuroprotection: survivalWithDMT, tetherDuration
  - EndogenousDMTRelease: stressCost, dmtReleaseRate
  - MAOAsRecall: dmtConcentration (exponential decay), excursionDuration
  - MAOInhibitorDuration: durationMultiplier, tetherRisk
  - DMNAsBoundaryCost: effectiveBoundaryCost, alphaCriticalFromCost
  - DMTMeditationSynergy: combinedCoupling, combinedControl
"""

import math
from dataclasses import dataclass
from typing import Optional

from . import PHI, ALPHA_EM

STRESS_EPSILON: float = 0.01


def tether_coupling(phase_diff: float) -> float:
    """Tether coupling strength kappa = cos(2*pi*Delta_Theta) * alpha_EM.
    From the paper, Definition 3 (Tether Coupling Strength)."""
    return math.cos(2.0 * math.pi * phase_diff) * ALPHA_EM


def activation_from_dose(dose: float) -> float:
    """Sig-1R activation level from DMT dose (sigmoid).
    Lean ref: Sigma1ReceptorModel.activationFromDose"""
    if dose <= 0:
        return 0.0
    return dose / (dose + 1.0)


def effective_barrier(coupling_barrier: float, activation: float) -> float:
    """Cellular J-cost barrier after Sig-1R activation.
    Lean ref: Sigma1ReceptorModel.effectiveBarrier"""
    return coupling_barrier * (1.0 - activation)


def stress_cost(oxygen_level: float) -> float:
    """Metabolic stress as a function of oxygen level (0=anoxia, 1=normoxia).
    Lean ref: EndogenousDMTRelease.stressCost"""
    return 1.0 / (oxygen_level + STRESS_EPSILON)


def dmt_release_rate(stress: float) -> float:
    """Endogenous DMT release rate as a function of stress.
    Lean ref: EndogenousDMTRelease.dmtReleaseRate"""
    if stress <= 0:
        return 0.0
    return stress / (stress + 1.0)


def survival_with_dmt(base_survival: float, activation: float) -> float:
    """Cell survival probability with DMT neuroprotection.
    Lean ref: DMTNeuroprotection.survivalWithDMT"""
    return base_survival + activation * (1.0 - base_survival)


def tether_duration(base_duration: float, activation: float) -> float:
    """Extended tether duration under DMT activation.
    Lean ref: DMTNeuroprotection.tetherDuration"""
    return base_duration * (1.0 + activation)


def dmt_concentration(initial: float, k_mao: float, t: float) -> float:
    """DMT concentration over time (exponential decay via MAO).
    Lean ref: MAOAsRecall.dmtConcentration"""
    return initial * math.exp(-k_mao * t)


def inhibited_mao_rate(k_mao: float, inhibition: float) -> float:
    """MAO degradation rate under MAOI.
    Lean ref: MAOAsRecall.inhibitedRate"""
    return k_mao * (1.0 - inhibition)


def excursion_duration(initial: float, threshold: float, k_mao: float) -> float:
    """Duration of excursion until DMT drops below threshold.
    Lean ref: MAOAsRecall.excursionDuration"""
    if k_mao <= 0 or initial <= threshold:
        return 0.0
    return math.log(initial / threshold) / k_mao


def duration_multiplier(inhibition: float) -> float:
    """Duration multiplier from MAOI.
    Lean ref: MAOInhibitorDuration.durationMultiplier"""
    if inhibition >= 1.0:
        return float("inf")
    return 1.0 / (1.0 - inhibition)


MAX_SAFE_DURATION_MINUTES: int = 240


def tether_risk(duration: float, risk_rate: float) -> float:
    """Cumulative tether decoherence risk.
    Lean ref: MAOInhibitorDuration.tetherRisk"""
    return 1.0 - math.exp(-risk_rate * duration)


def boundary_cost(base_cost: float, dmn_activity: float) -> float:
    """Effective boundary cost modulated by DMN suppression.
    Lean ref: DMNAsBoundaryCost.effectiveBoundaryCost"""
    return base_cost * dmn_activity


def alpha_critical(cost: float) -> float:
    """Critical excursion fraction for a given boundary cost.
    Lean ref: DMNAsBoundaryCost.alphaCriticalFromCost"""
    if cost <= 0:
        return 0.0
    return 1.0 - 1.0 / cost


def combined_coupling(flux: float, dmt_multiplier: float) -> float:
    """Meditation + DMT combined coupling.
    Lean ref: DMTMeditationSynergy.combinedCoupling"""
    alpha = 0.0 if flux <= 0 else flux / (flux + 1.0)
    return alpha * dmt_multiplier


def combined_control(meditation_skill: float, dmt_control: float) -> float:
    """Meditation + DMT combined control factor.
    Lean ref: DMTMeditationSynergy.combinedControl"""
    return dmt_control + meditation_skill * (1.0 - dmt_control)


CONSCIOUSNESS_RANKS = {
    "deep_sleep": 0,
    "light_sleep": 1,
    "dreaming": 2,
    "waking": 3,
    "focused": 4,
    "flow": 5,
    "meditation": 6,
    "dissolution": 7,
}


def dmt_effective_rank(dose: float) -> float:
    """Effective consciousness rank under DMT.
    Lean ref: DMTStateTransition.dmtEffectiveRank"""
    return 3.0 * (1.0 + dose)


@dataclass
class ExcursionProfile:
    dose: float
    activation: float
    effective_rank: float
    state_label: str
    barrier_reduction: float
    tether_strength: float
    survival_extension: float
    estimated_duration_min: float
    risk: float


def profile_excursion(
    dose: float,
    baseline_barrier: float = 5.0,
    baseline_survival: float = 0.7,
    baseline_duration_min: float = 15.0,
    k_mao: float = 0.1,
    risk_rate: float = 0.005,
    maoi_inhibition: float = 0.0,
) -> ExcursionProfile:
    """Compute a full excursion profile for a given DMT dose."""
    act = activation_from_dose(dose)
    eff_barrier = effective_barrier(baseline_barrier, act)
    eff_rank = dmt_effective_rank(dose)

    if eff_rank < 4:
        label = "sub-threshold"
    elif eff_rank < 6:
        label = "light"
    elif eff_rank < 8:
        label = "moderate"
    elif eff_rank < 15:
        label = "deep"
    else:
        label = "breakthrough"

    k_eff = inhibited_mao_rate(k_mao, maoi_inhibition)
    dur = excursion_duration(dose, 0.1, k_eff) if k_eff > 0 else float("inf")
    dur_min = dur / 60.0 if dur < float("inf") else float("inf")

    return ExcursionProfile(
        dose=dose,
        activation=act,
        effective_rank=eff_rank,
        state_label=label,
        barrier_reduction=1.0 - eff_barrier / baseline_barrier if baseline_barrier > 0 else 0.0,
        tether_strength=act,
        survival_extension=survival_with_dmt(baseline_survival, act) - baseline_survival,
        estimated_duration_min=dur_min,
        risk=tether_risk(dur_min, risk_rate) if dur_min < float("inf") else 1.0,
    )
