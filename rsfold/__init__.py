"""RS-Fold: Glass-box protein folding on the phi-lattice.

All geometric parameters derived from the golden ratio (zero free parameters).
Lean 4 proofs: IndisputableMonolith/ProteinFolding/
"""

__version__ = "0.1.0"

from .fold import fold, BackboneFirstFolder
from .constants import PHI, BACKBONE_DIST, HELIX_CA_I_I4
