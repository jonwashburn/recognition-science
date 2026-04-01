"""Derived geometric constants (from Lean proofs, not fitted).

Lean refs:
  - IndisputableMonolith/ProteinFolding/Derivations/D2_PhiGeometry.lean
  - IndisputableMonolith/ProteinFolding/Derivations/D2_PhiGeometryDerived.lean
  - IndisputableMonolith/Constants.lean
"""

import numpy as np

PHI: float = (1.0 + np.sqrt(5.0)) / 2.0
PHI_SQ: float = PHI ** 2
SQRT_PHI: float = np.sqrt(PHI)

CH_BOND: float = 1.09
NCA_BOND: float = 1.47
HBOND_LENGTH: float = PHI_SQ * CH_BOND         # ~2.85 A
BACKBONE_DIST: float = PHI_SQ * NCA_BOND       # ~3.85 A

HELIX_CA_I_I4: float = PHI * BACKBONE_DIST             # ~6.23 A
BETA_CA_INTERSTRAND: float = SQRT_PHI * BACKBONE_DIST   # ~4.90 A
HELIX_BUNDLE_DISTANCE: float = PHI_SQ * BACKBONE_DIST   # ~10.08 A
GENERIC_CA_CONTACT: float = HELIX_BUNDLE_DISTANCE

HELIX_PITCH: float = PHI ** 3.5    # ~5.39 A
BETA_RISE: float = PHI ** 2.5      # ~3.33 A

HELIX_RESIDUES_PER_TURN: float = 3.6
HELIX_HBOND_SKIP: int = 4
