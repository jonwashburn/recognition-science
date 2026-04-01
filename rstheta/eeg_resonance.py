"""EEG Theta Resonance Analyzer.

Detects the phi-resonance at 5*phi ~ 8.09 Hz in EEG time-series data.
This is falsifiable prediction P1 from the DMT Theta Field Interface paper.

Lean ref: IndisputableMonolith.Consciousness.DMT.DMTFrequencyTuning
  - carrierFreq = 5 * phi
  - dmtAmplification(f) = 1 / (1 + (f - carrierFreq)^2)  [Lorentzian peak]
  - THEOREM max_at_carrier: dmtAmplification(carrierFreq) = 1
"""

import math
from typing import List, Tuple, Optional
from dataclasses import dataclass

import numpy as np

from . import PHI, CARRIER_FREQ_HZ

THETA_BAND_LOW: float = 4.0
THETA_BAND_HIGH: float = 12.0


def lorentzian_amplification(freq: float) -> float:
    """RS theta-field amplification profile (Lorentzian centered at 5*phi Hz).
    Lean ref: DMTFrequencyTuning.dmtAmplification"""
    return 1.0 / (1.0 + (freq - CARRIER_FREQ_HZ) ** 2)


@dataclass
class ResonanceResult:
    carrier_freq: float
    peak_freq: float
    peak_power: float
    phi_resonance_ratio: float
    theta_band_power: float
    total_power: float
    theta_fraction: float
    frequencies: List[float]
    power_spectrum: List[float]
    rs_amplification: List[float]


def analyze_eeg(
    signal: np.ndarray,
    sample_rate: float = 256.0,
    window_seconds: float = 4.0,
) -> ResonanceResult:
    """Analyze an EEG signal for phi-resonance at 5*phi Hz.

    Args:
        signal: 1D array of EEG voltage samples.
        sample_rate: sampling rate in Hz (default 256).
        window_seconds: FFT window length in seconds (default 4).

    Returns:
        ResonanceResult with frequency analysis and phi-resonance score.
    """
    n_samples = len(signal)
    n_fft = int(sample_rate * window_seconds)
    if n_samples < n_fft:
        n_fft = n_samples

    n_windows = max(1, n_samples // n_fft)
    psd_accum = np.zeros(n_fft // 2 + 1)

    for w in range(n_windows):
        chunk = signal[w * n_fft : (w + 1) * n_fft]
        if len(chunk) < n_fft:
            break
        windowed = chunk * np.hanning(len(chunk))
        fft_vals = np.fft.rfft(windowed)
        psd_accum += np.abs(fft_vals) ** 2

    psd = psd_accum / max(n_windows, 1)
    freqs = np.fft.rfftfreq(n_fft, d=1.0 / sample_rate)

    theta_mask = (freqs >= THETA_BAND_LOW) & (freqs <= THETA_BAND_HIGH)
    theta_power = float(np.sum(psd[theta_mask]))
    total_power = float(np.sum(psd[1:]))

    carrier_idx = np.argmin(np.abs(freqs - CARRIER_FREQ_HZ))
    window_half = max(1, int(0.5 / (freqs[1] - freqs[0])) if len(freqs) > 1 else 1)
    lo = max(0, carrier_idx - window_half)
    hi = min(len(psd), carrier_idx + window_half + 1)
    phi_power = float(np.sum(psd[lo:hi]))

    peak_idx = lo + int(np.argmax(psd[lo:hi]))
    peak_freq = float(freqs[peak_idx])
    peak_power = float(psd[peak_idx])

    phi_ratio = phi_power / theta_power if theta_power > 0 else 0.0

    rs_amp = [lorentzian_amplification(float(f)) for f in freqs]

    return ResonanceResult(
        carrier_freq=CARRIER_FREQ_HZ,
        peak_freq=peak_freq,
        peak_power=peak_power,
        phi_resonance_ratio=phi_ratio,
        theta_band_power=theta_power,
        total_power=total_power,
        theta_fraction=theta_power / total_power if total_power > 0 else 0.0,
        frequencies=[float(f) for f in freqs],
        power_spectrum=[float(p) for p in psd],
        rs_amplification=rs_amp,
    )


def generate_mock_eeg(
    duration_seconds: float = 60.0,
    sample_rate: float = 256.0,
    phi_amplitude: float = 5.0,
    noise_amplitude: float = 10.0,
    seed: int = 42,
) -> np.ndarray:
    """Generate a synthetic EEG signal with an injected 5*phi Hz component.

    Use this to test that the analyzer correctly detects the phi-resonance."""
    rng = np.random.RandomState(seed)
    t = np.arange(0, duration_seconds, 1.0 / sample_rate)
    phi_signal = phi_amplitude * np.sin(2 * np.pi * CARRIER_FREQ_HZ * t)
    alpha_signal = 3.0 * np.sin(2 * np.pi * 10.0 * t)
    noise = noise_amplitude * rng.randn(len(t))
    return phi_signal + alpha_signal + noise
