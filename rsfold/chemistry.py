"""Amino acid chemistry table (matches ProteinFolding/Encoding/Chemistry.lean)."""

from dataclasses import dataclass
from typing import List


@dataclass
class AAChemistry:
    volume: float
    charge: float
    polarity: float
    h_donors: float
    h_acceptors: float
    aromaticity: float
    flexibility: float
    sulfur: float


AA_CHEM: dict[str, AAChemistry] = {
    "A": AAChemistry(0.15, 0.0, 0.0, 0.0, 0.0, 0.0, 0.9, 0.0),
    "G": AAChemistry(0.00, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0),
    "V": AAChemistry(0.35, 0.0, 0.0, 0.0, 0.0, 0.0, 0.4, 0.0),
    "L": AAChemistry(0.45, 0.0, 0.0, 0.0, 0.0, 0.0, 0.5, 0.0),
    "I": AAChemistry(0.45, 0.0, 0.0, 0.0, 0.0, 0.0, 0.3, 0.0),
    "P": AAChemistry(0.30, 0.0, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0),
    "C": AAChemistry(0.25, 0.0, 0.3, 0.5, 0.5, 0.0, 0.8, 1.0),
    "M": AAChemistry(0.45, 0.0, 0.2, 0.0, 0.5, 0.0, 0.7, 0.5),
    "F": AAChemistry(0.65, 0.0, 0.1, 0.0, 0.0, 1.0, 0.4, 0.0),
    "Y": AAChemistry(0.70, 0.0, 0.5, 0.5, 0.5, 1.0, 0.4, 0.0),
    "W": AAChemistry(1.00, 0.0, 0.4, 0.5, 0.5, 1.0, 0.3, 0.0),
    "H": AAChemistry(0.50, 0.5, 0.7, 0.5, 0.5, 1.0, 0.5, 0.0),
    "D": AAChemistry(0.35, -1.0, 0.9, 0.0, 1.0, 0.0, 0.7, 0.0),
    "E": AAChemistry(0.45, -1.0, 0.9, 0.0, 1.0, 0.0, 0.8, 0.0),
    "K": AAChemistry(0.50, 1.0, 0.8, 1.0, 0.0, 0.0, 0.9, 0.0),
    "R": AAChemistry(0.60, 1.0, 0.9, 1.0, 0.0, 0.0, 0.8, 0.0),
    "N": AAChemistry(0.35, 0.0, 0.8, 0.5, 1.0, 0.0, 0.7, 0.0),
    "Q": AAChemistry(0.45, 0.0, 0.8, 0.5, 1.0, 0.0, 0.8, 0.0),
    "S": AAChemistry(0.20, 0.0, 0.6, 0.5, 0.5, 0.0, 0.8, 0.0),
    "T": AAChemistry(0.30, 0.0, 0.5, 0.5, 0.5, 0.0, 0.6, 0.0),
}

CHANNEL_NAMES = [
    "volume", "charge", "polarity", "h_donors",
    "h_acceptors", "aromaticity", "flexibility", "sulfur",
]

CHANNEL_GETTERS = {
    "volume": lambda c: c.volume,
    "charge": lambda c: c.charge,
    "polarity": lambda c: c.polarity,
    "h_donors": lambda c: c.h_donors,
    "h_acceptors": lambda c: c.h_acceptors,
    "aromaticity": lambda c: c.aromaticity,
    "flexibility": lambda c: c.flexibility,
    "sulfur": lambda c: c.sulfur,
}


def encode_sequence(sequence: str) -> List[AAChemistry]:
    """Convert an amino acid string to a list of chemistry vectors."""
    return [AA_CHEM.get(aa, AA_CHEM["G"]) for aa in sequence.upper()]
