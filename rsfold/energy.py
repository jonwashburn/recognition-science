"""J-cost energy function and analytical gradient (from Cost/JcostCore.lean)."""

import numpy as np


def j_cost(r: float) -> float:
    """J(r) = (r + 1/r)/2 - 1.  The unique cost satisfying the RCL.
    Lean ref: IndisputableMonolith/Cost/JcostCore.lean"""
    if r <= 0.0:
        return 1000.0
    return 0.5 * (r + 1.0 / r) - 1.0


def j_cost_deriv(r: float) -> float:
    """dJ/dr = (1 - 1/r^2) / 2."""
    if r <= 0.0:
        return 0.0
    return 0.5 * (1.0 - 1.0 / (r * r))


def compute_rg(coords: np.ndarray) -> float:
    """Radius of gyration of a coordinate array (N x 3)."""
    center = coords.mean(axis=0)
    return float(np.sqrt(np.mean(np.sum((coords - center) ** 2, axis=1))))
