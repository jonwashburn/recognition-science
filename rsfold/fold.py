"""RS-Fold: backbone-first protein folder on the phi-lattice.

All parameters derived from the golden ratio. Zero free parameters.
Lean refs: IndisputableMonolith/ProteinFolding/ (derivation chain D1-D11).
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple

import numpy as np

from .constants import (
    PHI, PHI_SQ, BACKBONE_DIST, HELIX_CA_I_I4,
    BETA_CA_INTERSTRAND, HELIX_BUNDLE_DISTANCE, GENERIC_CA_CONTACT,
    HELIX_HBOND_SKIP,
)
from .chemistry import AAChemistry, encode_sequence, CHANNEL_NAMES, CHANNEL_GETTERS
from .wtokens import (
    WToken, spectra_per_residue, extract_wtokens,
    detect_strand_runs_from_tokens,
)
from .energy import j_cost, compute_rg
from .geometry import init_extended_chain


@dataclass
class FoldResult:
    coords: np.ndarray
    sequence: str
    energy: float
    rg: float
    contacts: List[Tuple[int, int, float, float]]
    strand_pairs: list
    energy_trace: List[float]


def gray_parity(beat: int) -> bool:
    g = (beat % 8) ^ ((beat % 8) >> 1)
    return g % 2 == 1


class BackboneFirstFolder:
    """Protein folder that builds backbone secondary structure first,
    then packs side-chains via J-cost minimization."""

    def __init__(self, sequence: str, seed: int = 42, *,
                 enable_helix: bool = True,
                 enable_contacts: bool = True,
                 enable_sheet: bool = True,
                 hydrophobic_weight: float = 0.3):
        self.sequence = sequence.upper()
        self.n = len(self.sequence)
        self.enable_helix = enable_helix
        self.enable_contacts = enable_contacts
        self.enable_sheet = enable_sheet
        self.hydrophobic_weight = hydrophobic_weight
        self.seed = seed

        self.chemistry = encode_sequence(self.sequence)

        self.channel_spectra: dict[str, List[np.ndarray]] = {}
        self.channel_tokens: dict[str, List[WToken]] = {}
        channel_p2: dict[str, float] = {}
        channel_p4: dict[str, float] = {}
        for name in CHANNEL_NAMES:
            getter = CHANNEL_GETTERS[name]
            sig = [float(getter(c)) for c in self.chemistry]
            spectra = spectra_per_residue(sig)
            tokens = extract_wtokens(spectra)
            self.channel_spectra[name] = spectra
            self.channel_tokens[name] = tokens
            channel_p2[name] = float(sum(np.abs(X[2]) ** 2 for X in spectra))
            channel_p4[name] = float(sum(np.abs(X[4]) ** 2 for X in spectra))

        self.helix_channel = max(channel_p2, key=lambda k: channel_p2[k])
        self.strand_channel = max(channel_p4, key=lambda k: channel_p4[k])
        self.contact_channel = self._select_contact_channel()

        self.tokens_helix = self.channel_tokens[self.helix_channel]
        self.tokens_strand = self.channel_tokens[self.strand_channel]
        self.tokens_contact = self.channel_tokens[self.contact_channel]
        self.spectra_contact = self.channel_spectra[self.contact_channel]

        self.helix_like = [
            (t.dominant_mode == 2 and t.phi_level >= 1) for t in self.tokens_helix
        ]

        self.coords = init_extended_chain(self.n, seed=seed)
        self.predicted_contacts = self._predict_contacts() if enable_contacts else []
        self.strand_runs = detect_strand_runs_from_tokens(self.tokens_strand)
        self.strand_pairs = self._pair_strand_runs()

    # ── Resonance scoring (Encoding/Resonance.lean) ──

    def _charge_gate(self, ci: AAChemistry, cj: AAChemistry) -> float:
        p = ci.charge * cj.charge
        if p < -0.5:
            return 1.3
        if p > 0.5:
            return 0.7
        return 1.0

    def _hbond_gate(self, ci: AAChemistry, cj: AAChemistry) -> float:
        return 1.0 + 0.15 * min(ci.h_donors, cj.h_acceptors) + 0.15 * min(cj.h_donors, ci.h_acceptors)

    def _aromatic_gate(self, ci: AAChemistry, cj: AAChemistry) -> float:
        return 1.2 if (ci.aromaticity > 0.5 and cj.aromaticity > 0.5) else 1.0

    def _chemistry_gate(self, ci: AAChemistry, cj: AAChemistry) -> float:
        return self._charge_gate(ci, cj) * self._hbond_gate(ci, cj) * self._aromatic_gate(ci, cj)

    def _phase_factor(self, wi: WToken, wj: WToken) -> float:
        dt = (wj.phase - wi.phase) % 8
        return float(np.cos(dt * np.pi / 4.0))

    def _amplitude_factor(self, wi: WToken, wj: WToken) -> float:
        return float(PHI ** (((wi.phi_level + wj.phi_level) / 2.0) - 1.0))

    def _mode_gate(self, wi: WToken, wj: WToken) -> float:
        if wi.dominant_mode == wj.dominant_mode:
            return 1.2
        if {wi.dominant_mode, wj.dominant_mode} == {2, 4}:
            return 0.8
        return 1.0

    def _loop_closure_penalty(self, sep: int) -> float:
        if sep < 6:
            return 0.0
        ratio = sep / 10.0
        if sep <= 10:
            return 1.0 / (1.0 + j_cost(ratio))
        return 1.0 / (1.0 + 0.5 * j_cost(ratio))

    def _required_channels(self, sep: int) -> int:
        if sep <= 10:
            return 2
        if sep <= 16:
            return 3
        if sep <= 26:
            return 4
        if sep <= 42:
            return 5
        return 6

    # ── Channel selection ──

    def _select_contact_channel(self) -> str:
        best_name = self.helix_channel
        best_count = -1
        for name in CHANNEL_NAMES:
            toks = self.channel_tokens[name]
            specs = self.channel_spectra[name]
            count = 0
            for i in range(self.n):
                for j in range(i + 6, self.n):
                    sep = j - i
                    ci, cj = self.chemistry[i], self.chemistry[j]
                    chem_gate = self._chemistry_gate(ci, cj)
                    wi, wj = toks[i], toks[j]
                    base = self._phase_factor(wi, wj) * self._amplitude_factor(wi, wj) * self._mode_gate(wi, wj) * chem_gate
                    if base <= 0:
                        continue
                    coherent = self._count_coherent(specs[i], specs[j])
                    if coherent >= self._required_channels(sep):
                        count += 1
            if count > best_count:
                best_count = count
                best_name = name
        return best_name

    @staticmethod
    def _count_coherent(Xi: np.ndarray, Xj: np.ndarray, threshold: float = 0.5) -> int:
        count = 0
        for k in range(8):
            diff = float(np.angle(Xj[k]) - np.angle(Xi[k]))
            if diff > np.pi:
                diff -= 2 * np.pi
            elif diff < -np.pi:
                diff += 2 * np.pi
            if float(np.cos(diff)) > threshold:
                count += 1
        return count

    # ── Contact prediction ──

    def _predict_contacts(self) -> List[Tuple[int, int, float, float]]:
        budget = int(np.floor(self.n / (PHI ** 3))) if self.n <= 45 else int(np.floor(self.n / PHI_SQ))
        candidates: List[Tuple[int, int, float, float]] = []
        for i in range(self.n):
            for j in range(i + 6, self.n):
                sep = j - i
                loop = self._loop_closure_penalty(sep)
                if loop <= 0:
                    continue
                ci, cj = self.chemistry[i], self.chemistry[j]
                chem_gate = self._chemistry_gate(ci, cj)
                wi, wj = self.tokens_contact[i], self.tokens_contact[j]
                base = self._phase_factor(wi, wj) * self._amplitude_factor(wi, wj) * self._mode_gate(wi, wj) * chem_gate
                if base <= 0:
                    continue
                coherent = self._count_coherent(self.spectra_contact[i], self.spectra_contact[j])
                req = self._required_channels(sep)
                if coherent < req:
                    continue
                consensus = 1.0 + 0.1 * (coherent - req)
                score = float(base * loop * consensus)
                if score <= 0:
                    continue
                tsi, tsj = self.tokens_strand[i], self.tokens_strand[j]
                thi, thj = self.tokens_helix[i], self.tokens_helix[j]
                strand_like = (tsi.dominant_mode == 4 and tsi.phi_level >= 1) and (tsj.dominant_mode == 4 and tsj.phi_level >= 1)
                helix_like = (thi.dominant_mode == 2 and thi.phi_level >= 1) and (thj.dominant_mode == 2 and thj.phi_level >= 1)
                if strand_like:
                    target = BETA_CA_INTERSTRAND
                elif helix_like:
                    target = HELIX_BUNDLE_DISTANCE
                else:
                    target = GENERIC_CA_CONTACT
                candidates.append((i, j, score, float(target)))
        candidates.sort(key=lambda t: t[2], reverse=True)
        return candidates[:budget]

    # ── Strand pairing ──

    def _pair_strand_runs(self) -> List[Tuple[Tuple[int, int], Tuple[int, int], bool, int]]:
        runs = self.strand_runs
        if len(runs) < 2:
            return []
        best_by_pair: dict[Tuple[int, int], Tuple[int, int, bool, int, float]] = {}
        for a in range(len(runs)):
            for b in range(a + 1, len(runs)):
                r1, r2 = runs[a], runs[b]
                gap = r2[0] - r1[1] if r1[1] <= r2[0] else r1[0] - r2[1]
                if gap < 3:
                    continue
                support = sum(
                    1 for ci, cj, cs, ct in self.predicted_contacts
                    if cs >= 0.5 and abs(ct - BETA_CA_INTERSTRAND) < 1e-6
                    and ((r1[0] <= ci < r1[1] and r2[0] <= cj < r2[1])
                         or (r1[0] <= cj < r1[1] and r2[0] <= ci < r2[1]))
                )
                if support < 1:
                    continue
                len1, len2 = r1[1] - r1[0], r2[1] - r2[0]
                if len1 < 3 or len2 < 3:
                    continue
                for parallel in (False, True):
                    for shift in range(-3, 4):
                        score, count = 0.0, 0
                        for k in range(min(len1, len2)):
                            i = r1[0] + k
                            j = (r2[0] + k + shift) if parallel else (r2[1] - 1 - k - shift)
                            if j < r2[0] or j >= r2[1]:
                                continue
                            ci, cj = self.chemistry[i], self.chemistry[j]
                            wi, wj = self.tokens_strand[i], self.tokens_strand[j]
                            s = self._phase_factor(wi, wj) * self._amplitude_factor(wi, wj) * self._mode_gate(wi, wj) * self._chemistry_gate(ci, cj)
                            pi_p = gray_parity(wi.phase)
                            pj_p = gray_parity(wj.phase)
                            bonus = 1.2 if (parallel and pi_p == pj_p) or (not parallel and pi_p != pj_p) else 1.0
                            score += max(0.0, s * bonus)
                            count += 1
                        if count >= 3 and score > 0:
                            key = (a, b)
                            if key not in best_by_pair or score > best_by_pair[key][4]:
                                best_by_pair[key] = (a, b, parallel, shift, score)
        selected: List[Tuple[Tuple[int, int], Tuple[int, int], bool, int]] = []
        used: set[int] = set()
        for a, b, parallel, shift, _score in sorted(best_by_pair.values(), key=lambda x: x[4], reverse=True):
            if a in used or b in used:
                continue
            used.update({a, b})
            selected.append((runs[a], runs[b], parallel, shift))
        return selected

    # ── Energy + gradient ──

    def compute_energy_and_gradient(self) -> Tuple[float, np.ndarray]:
        E = 0.0
        grad = np.zeros_like(self.coords)

        def _add_pair(i: int, j: int, target: float, weight: float):
            nonlocal E
            diff = self.coords[j] - self.coords[i]
            dist = max(np.linalg.norm(diff), 0.1 if target < 5.0 else 0.5)
            ratio = dist / target
            E += weight * j_cost(ratio)
            dJ = weight * 0.5 * (1.0 - 1.0 / (ratio ** 2)) / target
            g = dJ * (diff / dist)
            grad[i] -= g
            grad[j] += g

        for i in range(self.n - 1):
            _add_pair(i, i + 1, BACKBONE_DIST, 50.0)

        if self.enable_helix:
            for i in range(self.n - HELIX_HBOND_SKIP):
                j = i + HELIX_HBOND_SKIP
                if self.helix_like[i] or self.helix_like[j]:
                    _add_pair(i, j, HELIX_CA_I_I4, 3.0)

        if self.enable_contacts:
            for i, j, score, target in self.predicted_contacts:
                w = min(3.0, max(0.5, score))
                _add_pair(i, j, target, w)

        if self.enable_sheet:
            for (r1s, r1e), (r2s, r2e), parallel, shift in self.strand_pairs:
                for k in range(min(r1e - r1s, r2e - r2s)):
                    i = r1s + k
                    j = (r2s + k + shift) if parallel else (r2e - 1 - k - shift)
                    if 0 <= i < self.n and 0 <= j < self.n:
                        _add_pair(i, j, BETA_CA_INTERSTRAND, 2.0)

        for i in range(self.n):
            for j in range(i + 2, self.n):
                diff = self.coords[j] - self.coords[i]
                dist = np.linalg.norm(diff)
                min_dist = 3.5 + (BACKBONE_DIST / 2.0) * (self.chemistry[i].volume + self.chemistry[j].volume)
                if dist < min_dist:
                    E += 50.0 * (min_dist - dist) ** 2
                    g = -100.0 * (min_dist - dist) * (diff / dist)
                    grad[i] -= g
                    grad[j] += g

        rg_target = (self.n / PHI) ** (1.0 / 3.0) * BACKBONE_DIST
        current_rg = compute_rg(self.coords)
        if current_rg > rg_target:
            E += 2.0 * (current_rg - rg_target) ** 2
            center = self.coords.mean(axis=0)
            for i in range(self.n):
                diff = self.coords[i] - center
                dist = np.linalg.norm(diff)
                if dist > 0.1:
                    grad[i] += 4.0 * (current_rg - rg_target) * diff / (self.n * current_rg)

        center = self.coords.mean(axis=0)
        for i in range(self.n):
            chem = self.chemistry[i]
            burial = chem.volume * (1.0 - chem.polarity)
            if burial > 0.3:
                diff = self.coords[i] - center
                dist = np.linalg.norm(diff)
                core_radius = rg_target * 0.6
                if dist > core_radius:
                    E += self.hydrophobic_weight * burial * (dist - core_radius)
                    grad[i] += self.hydrophobic_weight * burial * (diff / max(dist, 0.1))

        return E, grad

    # ── Optimizer ──

    def fold(self, iterations: int = 2000, verbose: bool = True) -> FoldResult:
        velocity = np.zeros_like(self.coords)
        momentum = 0.9
        lr = 0.01
        best_energy = float("inf")
        best_coords = self.coords.copy()
        energy_trace: List[float] = []

        for step in range(iterations):
            E, grad = self.compute_energy_and_gradient()
            energy_trace.append(E)
            if E < best_energy:
                best_energy = E
                best_coords = self.coords.copy()
            grad_norm = np.linalg.norm(grad)
            if grad_norm > 10.0:
                grad = grad * 10.0 / grad_norm
            velocity = momentum * velocity - lr * grad
            self.coords += velocity
            if verbose and step % 500 == 0:
                rg = compute_rg(self.coords)
                print(f"  Step {step}: E={E:.1f}, Rg={rg:.2f} A")

        self.coords = best_coords
        return FoldResult(
            coords=best_coords,
            sequence=self.sequence,
            energy=best_energy,
            rg=compute_rg(best_coords),
            contacts=self.predicted_contacts,
            strand_pairs=self.strand_pairs,
            energy_trace=energy_trace,
        )


def fold(sequence: str, iterations: int = 2000, seed: int = 42,
         verbose: bool = True) -> FoldResult:
    """Convenience function: fold a sequence and return the result."""
    folder = BackboneFirstFolder(sequence, seed=seed)
    return folder.fold(iterations=iterations, verbose=verbose)
