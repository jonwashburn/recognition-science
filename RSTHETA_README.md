# RS-Theta: Theta Field Interface Toolkit

**Open-source tools for consciousness state analysis from first principles.**

Every formula in this package traces to a machine-verified Lean 4 proof.
17 modules. Zero `sorry`. Zero free parameters.

## What This Is

RS-Theta implements the mathematical models from the paper:

> **The Molecular Key to the Theta Field: A Zero-Parameter Formalization of Endogenous DMT and Consciousness State Transitions**
> (Washburn, 2026 — [PDF included](DMT_Theta_Field_Interface.pdf))

The key prediction: DMT preferentially amplifies EEG power at **5*phi = 8.09 Hz**, the carrier frequency of the theta field.

## Install

```bash
git clone https://github.com/jonwashburn/recognition-science.git
cd recognition-science
pip install numpy   # only dependency
```

## CLI Commands

### 1. EEG Phi-Resonance Analyzer

Detect the 5*phi Hz signal in EEG data:

```bash
# With your own EEG data (CSV, one column of voltage samples):
python -m rstheta.cli analyze-eeg --file subject1.csv --sample-rate 256

# With synthetic demo data (injected 8.09 Hz signal):
python -m rstheta.cli analyze-eeg
```

### 2. Tryptamine Phi-Ladder

Map any tryptamine to its phi-ladder rung:

```bash
# All known tryptamines:
python -m rstheta.cli ladder

# Specific molecule:
python -m rstheta.cli ladder --molecule DMT

# Design an analog for a specific rung:
python -m rstheta.cli ladder --design-rung 3
```

### 3. Tethered Excursion Profiler

Compute safety bounds and excursion depth:

```bash
# Standard DMT dose:
python -m rstheta.cli excursion --dose 1.0

# With MAOI (ayahuasca-like):
python -m rstheta.cli excursion --dose 0.5 --maoi 0.8
```

### 4. Neuroprotection Model

Simulate the cardiac arrest -> endogenous DMT -> Sig-1R cascade:

```bash
python -m rstheta.cli neuroprotection
```

## Python API

```python
from rstheta import PHI, CARRIER_FREQ_HZ
from rstheta.eeg_resonance import analyze_eeg, generate_mock_eeg
from rstheta.tryptamine_ladder import analyze_molecule, design_analog
from rstheta.tether_mechanics import profile_excursion
from rstheta.sig1r_gating import model_cardiac_arrest

# EEG analysis
signal = generate_mock_eeg(duration_seconds=60)
result = analyze_eeg(signal, sample_rate=256)
print(f"Peak at {result.peak_freq:.2f} Hz (carrier = {result.carrier_freq:.2f} Hz)")

# Tryptamine analysis
dmt = analyze_molecule("DMT", 188.27)
print(f"DMT: rung={dmt.half_rung}, balance={dmt.balance:.6f}")

# Design a new analog
target = design_analog(target_half_rung=3)
print(f"Target MW: {target['target_mw']:.1f} Da")

# Excursion profile
exc = profile_excursion(dose=1.0)
print(f"State: {exc.state_label}, risk: {exc.risk:.4f}")

# Neuroprotection cascade
cascade = model_cardiac_arrest()
for r in cascade:
    print(f"O2={r.oxygen_fraction:.2f} -> survival={r.survival_with_dmt:.4f}")
```

## Falsifiable Predictions

This toolkit implements 4 testable predictions from the paper:

| Prediction | Test | Module |
|-----------|------|--------|
| **P1**: EEG power peaks at 5*phi = 8.09 Hz during DMT | Bandpass + FFT on psychedelic trial data | `eeg_resonance.py` |
| **P2**: Faraday cage attenuates inter-subject theta coherence | Shielded vs unshielded EEG comparison | (experimental protocol) |
| **P3**: Tryptamine analogs space at discrete phi-ladder half-rungs | MW ratio analysis | `tryptamine_ladder.py` |
| **P4**: Pinealectomy does NOT prevent DMT release | Already confirmed (Borjigin 2019) | (literature) |

## Lean 4 Module Index

Every function in this package has a Lean 4 proof anchor:

| Python module | Lean namespace | Key theorems |
|--------------|---------------|-------------|
| `eeg_resonance.py` | `DMTFrequencyTuning` | `max_at_carrier`, `prediction_holds` |
| `tryptamine_ladder.py` | `DMTPhiLadder`, `OptimalAnalogDesign` | `dmt_golden_balance`, `rpow_balance`, `discrete_family` |
| `tether_mechanics.py` | `DMTTetherMechanism`, `DMTNeuroprotection`, `MAOAsRecall` | `THEOREM_dmt_tether_safe`, `dmt_extends_tether` |
| `sig1r_gating.py` | `Sigma1ReceptorModel`, `DMTNeuroprotection` | `dose_monotone`, `neuroprotection_is_tether_maintenance` |

## Epistemic Boundary

This toolkit distinguishes between:

- **FORCED (Lean-proved)**: J-cost uniqueness, phi-ladder geometry, 8-tick cycle, theta field existence
- **MODEL (consistent, testable)**: DMT-to-phi^1 rung mapping, Sig-1R as barrier modulator, NDE-to-theta injection
- **PREDICTION (falsifiable)**: 8.09 Hz EEG peak, Faraday attenuation, analog spacing, pinealectomy invariance

The Lean proofs verify that the biological model is *strictly consistent* with the forced physics. They do not prove the biology is inevitable.

## License

MIT

## Author

Jonathan Washburn — Recognition Science Research Institute
