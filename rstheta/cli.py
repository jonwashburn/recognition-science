"""RS-Theta command-line interface."""

import argparse
import json
import sys

import numpy as np

from . import __version__, PHI, CARRIER_FREQ_HZ
from .eeg_resonance import analyze_eeg, generate_mock_eeg
from .tryptamine_ladder import analyze_molecule, analyze_all_known, design_analog, KNOWN_TRYPTAMINES
from .tether_mechanics import profile_excursion
from .sig1r_gating import model_cardiac_arrest


def cmd_eeg(args):
    print(f"RS-Theta EEG Analyzer v{__version__}")
    print(f"Carrier frequency: 5*phi = {CARRIER_FREQ_HZ:.4f} Hz")
    print()

    if args.file:
        data = np.loadtxt(args.file, delimiter=",")
        if data.ndim > 1:
            data = data[:, args.column]
        signal = data.astype(float)
        print(f"Loaded {len(signal)} samples from {args.file}")
    else:
        print("No file provided. Generating mock EEG with injected 8.09 Hz signal...")
        signal = generate_mock_eeg(
            duration_seconds=args.duration,
            sample_rate=args.sample_rate,
            phi_amplitude=5.0,
        )
        print(f"Generated {len(signal)} samples ({args.duration}s at {args.sample_rate} Hz)")

    result = analyze_eeg(signal, sample_rate=args.sample_rate)

    print(f"\n--- Phi-Resonance Analysis ---")
    print(f"Peak frequency:       {result.peak_freq:.3f} Hz")
    print(f"RS carrier (5*phi):   {result.carrier_freq:.4f} Hz")
    print(f"Peak power:           {result.peak_power:.2f}")
    print(f"Phi-resonance ratio:  {result.phi_resonance_ratio:.4f}")
    print(f"Theta band power:     {result.theta_band_power:.2f}")
    print(f"Theta fraction:       {result.theta_fraction:.4f}")

    if args.output:
        out = {
            "carrier_freq": result.carrier_freq,
            "peak_freq": result.peak_freq,
            "peak_power": result.peak_power,
            "phi_resonance_ratio": result.phi_resonance_ratio,
            "theta_band_power": result.theta_band_power,
            "theta_fraction": result.theta_fraction,
        }
        with open(args.output, "w") as f:
            json.dump(out, f, indent=2)
        print(f"\nSaved to {args.output}")


def cmd_ladder(args):
    print(f"RS-Theta Tryptamine Phi-Ladder v{__version__}")
    print(f"phi = {PHI:.6f}")
    print()

    if args.molecule:
        name = args.molecule
        mw = KNOWN_TRYPTAMINES.get(name)
        if mw is None:
            if args.mw:
                mw = args.mw
            else:
                print(f"Unknown molecule '{name}'. Use --mw to specify molecular weight.")
                sys.exit(1)
        p = analyze_molecule(name, mw)
        _print_profile(p)
    elif args.design_rung is not None:
        d = design_analog(args.design_rung)
        print(f"--- Designed Analog (half-rung {d['half_rung']}) ---")
        for k, v in d.items():
            print(f"  {k}: {v}")
    else:
        profiles = analyze_all_known()
        print(f"{'Name':<14} {'MW':>7} {'Ratio':>6} {'J-cost':>7} {'Rung':>5} {'Coupling':>9} {'Control':>9} {'Balance':>8}")
        print("-" * 78)
        for p in profiles:
            print(f"{p.name:<14} {p.molecular_weight:>7.1f} {p.serotonin_ratio:>6.3f} "
                  f"{p.j_cost_vs_serotonin:>7.4f} {p.half_rung:>5} "
                  f"{p.coupling:>9.4f} {p.control:>9.4f} {p.balance:>8.4f}")

    if args.output:
        profiles = analyze_all_known()
        out = [vars(p) for p in profiles]
        with open(args.output, "w") as f:
            json.dump(out, f, indent=2)
        print(f"\nSaved to {args.output}")


def _print_profile(p):
    print(f"--- {p.name} ---")
    print(f"  Molecular weight:     {p.molecular_weight:.2f} Da")
    print(f"  Serotonin ratio:      {p.serotonin_ratio:.4f}")
    print(f"  J-cost vs serotonin:  {p.j_cost_vs_serotonin:.6f}")
    print(f"  Phi-ladder half-rung: {p.half_rung}")
    print(f"  Coupling (phi^r/2):   {p.coupling:.4f}")
    print(f"  Control (phi^-r/2):   {p.control:.4f}")
    print(f"  Balance (c*k):        {p.balance:.6f}")
    print(f"  Effective rank @1x:   {p.effective_rank_at_dose_1:.1f}")
    print(f"  Predicted depth:      {p.predicted_depth}")


def cmd_excursion(args):
    print(f"RS-Theta Excursion Profiler v{__version__}")
    print()

    p = profile_excursion(
        dose=args.dose,
        maoi_inhibition=args.maoi,
    )

    print(f"--- Excursion Profile ---")
    print(f"  Dose:                 {p.dose:.2f}")
    print(f"  Sig-1R activation:    {p.activation:.4f}")
    print(f"  Effective rank:       {p.effective_rank:.1f}")
    print(f"  State:                {p.state_label}")
    print(f"  Barrier reduction:    {p.barrier_reduction:.1%}")
    print(f"  Tether strength:      {p.tether_strength:.4f}")
    print(f"  Survival extension:   +{p.survival_extension:.4f}")
    print(f"  Est. duration (min):  {p.estimated_duration_min:.1f}")
    print(f"  Decoherence risk:     {p.risk:.4f}")

    if args.output:
        with open(args.output, "w") as f:
            json.dump(vars(p), f, indent=2)
        print(f"\nSaved to {args.output}")


def cmd_neuroprotection(args):
    print(f"RS-Theta Neuroprotection Model v{__version__}")
    print("Simulating cardiac arrest: normoxia -> anoxia")
    print()

    results = model_cardiac_arrest()

    print(f"{'O2':>5} {'Stress':>8} {'DMT Rel':>8} {'Sig1R':>6} "
          f"{'Barrier%':>9} {'Surv':>6} {'Surv+DMT':>9} {'Gain':>6} {'Cluster':>8}")
    print("-" * 82)
    for r in results:
        print(f"{r.oxygen_fraction:>5.2f} {r.stress:>8.1f} {r.endogenous_dmt_release:>8.4f} "
              f"{r.sig1r_activation:>6.4f} {r.barrier_reduction_pct:>8.1f}% "
              f"{r.survival_without_dmt:>6.2f} {r.survival_with_dmt:>9.4f} "
              f"+{r.survival_gain:>5.4f} {r.cluster_amplification:>8}")

    if args.output:
        out = [vars(r) for r in results]
        with open(args.output, "w") as f:
            json.dump(out, f, indent=2)
        print(f"\nSaved to {args.output}")


def main():
    parser = argparse.ArgumentParser(
        prog="rs_theta",
        description="RS-Theta: Theta Field Interface Toolkit",
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    sub = parser.add_subparsers(dest="command")

    p_eeg = sub.add_parser("analyze-eeg", help="Analyze EEG for phi-resonance at 5*phi Hz")
    p_eeg.add_argument("--file", "-f", type=str, default="")
    p_eeg.add_argument("--column", "-c", type=int, default=0)
    p_eeg.add_argument("--sample-rate", type=float, default=256.0)
    p_eeg.add_argument("--duration", type=float, default=60.0)
    p_eeg.add_argument("--output", "-o", type=str, default="")

    p_lad = sub.add_parser("ladder", help="Tryptamine phi-ladder analysis")
    p_lad.add_argument("--molecule", "-m", type=str, default="")
    p_lad.add_argument("--mw", type=float, default=0.0)
    p_lad.add_argument("--design-rung", type=int, default=None)
    p_lad.add_argument("--output", "-o", type=str, default="")

    p_exc = sub.add_parser("excursion", help="Profile a tethered excursion")
    p_exc.add_argument("--dose", "-d", type=float, default=1.0)
    p_exc.add_argument("--maoi", type=float, default=0.0)
    p_exc.add_argument("--output", "-o", type=str, default="")

    p_neuro = sub.add_parser("neuroprotection", help="Cardiac arrest neuroprotection model")
    p_neuro.add_argument("--output", "-o", type=str, default="")

    args = parser.parse_args()
    if args.command == "analyze-eeg":
        cmd_eeg(args)
    elif args.command == "ladder":
        cmd_ladder(args)
    elif args.command == "excursion":
        cmd_excursion(args)
    elif args.command == "neuroprotection":
        cmd_neuroprotection(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
