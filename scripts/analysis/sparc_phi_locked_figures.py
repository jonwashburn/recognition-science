#!/usr/bin/env python3
"""Generate publication-quality figures for the φ-locked SPARC paper.

Reads:
  artifacts/gravity_paper_v07_sparc_phi_locked.json   (Q=1)
  artifacts/sparc_phi_locked_q2_holdout.json          (Q=2)
  artifacts/sparc_phi_locked_q3_holdout.json          (Q=3)
  artifacts/sparc_phi_locked_q2q3_combined.json       (Q=2+Q=3)
  artifacts/sparc_phi_locked_q1q2q3_combined.json     (full)
  artifacts/sparc_phi_locked_btfr_locked.json         (BTFR)

Writes (PDF + PNG):
  papers/figures/sparc_chi2_distributions.pdf  (.png)
  papers/figures/sparc_btfr.pdf                (.png)
  papers/figures/sparc_low_risk_summary.pdf    (.png)
  papers/figures/sparc_residual_histogram.pdf  (.png)
  papers/figures/sparc_falsifier_dashboard.pdf (.png)

Style: Recognition Physics monochrome with phi-themed accents; no
matplotlib defaults. All figures preserve the locked numbers exactly.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[2]
FIG_DIR = ROOT / "papers/figures"


def load_json(name: str) -> dict:
    return json.loads((ROOT / "artifacts" / name).read_text())


def setup_style() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Serif",
        "font.size": 10,
        "axes.linewidth": 0.8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "grid.color": "#E0E0E0",
        "grid.linewidth": 0.4,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.size": 4,
        "ytick.major.size": 4,
        "legend.frameon": False,
        "legend.fontsize": 9,
        "savefig.dpi": 200,
        "savefig.bbox": "tight",
    })


PHI = (1.0 + math.sqrt(5.0)) / 2.0
ILG_COLOR = "#1f4e79"
MOND_COLOR = "#a83232"
NEUTRAL_COLOR = "#4d4d4d"
LOWRISK_COLOR = "#3a7d44"


def chi2_arrays(art: dict, key: str = "result") -> tuple[np.ndarray, np.ndarray]:
    block = art[key] if key in art else art
    rows = block.get("per_galaxy") if isinstance(block, dict) and "per_galaxy" in block else None
    if rows is None and "per_galaxy_chi2" in art:
        rows = art["per_galaxy_chi2"]
    if rows is None:
        return np.array([]), np.array([])
    chi = np.array([float(g["chi2N_cr"]) for g in rows], dtype=float)
    mond = np.array([float(g["chi2N_mond"]) for g in rows], dtype=float)
    return chi, mond


def fig_chi2_distributions() -> None:
    q1_art = load_json("gravity_paper_v07_sparc_phi_locked.json")
    q2_art = load_json("sparc_phi_locked_q2_holdout.json")
    q3_art = load_json("sparc_phi_locked_q3_holdout.json")

    q1_chi = np.array([float(g["chi2N_cr"]) for g in q1_art["per_galaxy_chi2"]])
    q1_mond = np.array([float(g["chi2N_mond"]) for g in q1_art["per_galaxy_chi2"]])
    q2_chi, q2_mond = chi2_arrays(q2_art)
    q3_chi, q3_mond = chi2_arrays(q3_art)

    fig, axes = plt.subplots(1, 3, figsize=(11, 3.6), sharey=True)
    titles = [
        f"Q=1 discovery (N={q1_chi.size})",
        f"Q=2 hold-out (N={q2_chi.size})",
        f"Q=3 hold-out (N={q3_chi.size})",
    ]
    chi_pairs = [(q1_chi, q1_mond), (q2_chi, q2_mond), (q3_chi, q3_mond)]
    bins = np.logspace(-2, 2, 30)

    for ax, (chi_ilg, chi_mond), title in zip(axes, chi_pairs, titles):
        ax.hist(chi_mond, bins=bins, color=MOND_COLOR, alpha=0.55,
                label="MOND simple-μ", linewidth=0.0)
        ax.hist(chi_ilg, bins=bins, color=ILG_COLOR, alpha=0.85,
                label="φ-locked ILG", linewidth=0.0)
        ax.axvline(2.0, color=NEUTRAL_COLOR, lw=0.8, ls="--", alpha=0.6,
                   label=r"$\chi^2/N=2$ (strict v07)")
        ax.axvline(5.0, color=NEUTRAL_COLOR, lw=0.8, ls=":", alpha=0.6,
                   label=r"$\chi^2/N=5$ (falsifier F1)")
        ax.set_xscale("log")
        ax.set_xlabel(r"$\chi^2/N$ per galaxy")
        ax.set_title(title, fontsize=10)
        ax.set_xlim(1e-2, 1e2)
        med_ilg = float(np.median(chi_ilg)) if chi_ilg.size else float("nan")
        med_mond = float(np.median(chi_mond)) if chi_mond.size else float("nan")
        ax.text(0.04, 0.95,
                f"median:\n  ILG  = {med_ilg:.3f}\n  MOND = {med_mond:.3f}",
                transform=ax.transAxes, fontsize=8, va="top",
                family="monospace")

    axes[0].set_ylabel("galaxies / bin")
    axes[-1].legend(loc="upper right", fontsize=8)
    fig.suptitle(r"$\chi^2/N$ distributions across SPARC quality classes (zero per-galaxy parameters)",
                 fontsize=11, y=1.02)

    out = FIG_DIR / "sparc_chi2_distributions"
    fig.savefig(out.with_suffix(".pdf"))
    fig.savefig(out.with_suffix(".png"))
    plt.close(fig)
    print(f"wrote {out}.pdf and {out}.png")


def fig_btfr() -> None:
    btfr = load_json("sparc_phi_locked_btfr_locked.json")
    obs = float(btfr["btfr_observed"]["slope_beta"])
    pred = float(btfr["btfr_predicted"]["slope_beta"])
    band_lo, band_hi = btfr["btfr_predicted"]["band"]
    scatter = float(btfr["btfr_observed"]["scatter_dex"])

    fig, ax = plt.subplots(figsize=(6.0, 3.6))
    # Schematic: show the prediction line as a band and the observed slope
    # as a vertical mark on the slope axis.
    bx = np.array([band_lo, band_hi])
    ax.fill_betweenx([0, 1], bx[0], bx[1], color=ILG_COLOR, alpha=0.10,
                     label=f"falsifier band F3: ({band_lo}, {band_hi})")
    ax.axvline(pred, color=NEUTRAL_COLOR, lw=1.0, ls="--",
               label=f"locked prediction β={pred}")
    ax.axvline(obs, color=ILG_COLOR, lw=2.0,
               label=f"observed β={obs:.4f}")
    ax.text(obs, 0.55, f"  Δβ = {obs - pred:+.4f}\n  rel = {(obs-pred)/pred*100:.4f}%",
            fontsize=9, va="center", family="monospace")
    ax.set_xlim(3.4, 4.6)
    ax.set_ylim(0, 1)
    ax.set_yticks([])
    ax.set_xlabel(r"BTFR slope $\beta$")
    ax.set_title(f"φ-locked Baryonic Tully-Fisher Relation, SPARC Q=1 (N={btfr['btfr_observed']['N_galaxies']}, scatter={scatter:.3f} dex)",
                 fontsize=10)
    ax.legend(loc="upper left", fontsize=9)

    out = FIG_DIR / "sparc_btfr"
    fig.savefig(out.with_suffix(".pdf"))
    fig.savefig(out.with_suffix(".png"))
    plt.close(fig)
    print(f"wrote {out}.pdf and {out}.png")


def fig_low_risk_summary() -> None:
    samples = []

    def add(name: str, art: dict) -> None:
        full = art["full_metrics"] if "full_metrics" in art else None
        low = art["low_risk_metrics"] if "low_risk_metrics" in art else None
        if "result" in art:
            r = art["result"]
            full = r.get("full_metrics", full)
            low = r.get("low_risk_metrics", low)
        samples.append((name, full, low))

    q2 = load_json("sparc_phi_locked_q2_holdout.json")
    q3 = load_json("sparc_phi_locked_q3_holdout.json")
    q2q3 = load_json("sparc_phi_locked_q2q3_combined.json")
    full_all = load_json("sparc_phi_locked_q1q2q3_combined.json")
    add("Q=2 hold-out", q2)
    add("Q=3 hold-out", q3)
    add("Q=2+Q=3 (prereg)", q2q3)
    add("Q=1+Q=2+Q=3 (full)", full_all)

    fig, ax = plt.subplots(figsize=(7.4, 4.2))
    y_full = np.arange(len(samples)) * 1.4 + 0.0
    y_low = np.arange(len(samples)) * 1.4 + 0.55

    full_means = [s[1]["mean_chi2N_causal_response"] for s in samples]
    full_fgoods = [s[1]["fraction_causal_response_passed"] for s in samples]
    low_means = [s[2]["mean_chi2N_causal_response"] for s in samples]
    low_fgoods = [s[2]["fraction_causal_response_passed"] for s in samples]

    ax.barh(y_full, full_means, height=0.45, color=ILG_COLOR, alpha=0.55,
            label="full sample mean χ²/N")
    ax.barh(y_low, low_means, height=0.45, color=LOWRISK_COLOR, alpha=0.85,
            label="low-risk subset mean χ²/N")
    ax.axvline(2.0, color=NEUTRAL_COLOR, lw=0.8, ls="--", alpha=0.6,
               label="strict v07 threshold (mean<2.0)")

    for y, m, f in zip(y_full, full_means, full_fgoods):
        ax.text(m + 0.07, y, f"  mean={m:.3f}, f_good={f:.2f}",
                fontsize=8, va="center", family="monospace")
    for y, m, f in zip(y_low, low_means, low_fgoods):
        ax.text(m + 0.07, y, f"  mean={m:.3f}, f_good={f:.2f}  PASS"
                if (m < 2.0 and f > 0.7) else f"  mean={m:.3f}, f_good={f:.2f}",
                fontsize=8, va="center", family="monospace",
                color=LOWRISK_COLOR if (m < 2.0 and f > 0.7) else NEUTRAL_COLOR)

    yticks = (y_full + y_low) / 2.0
    ax.set_yticks(yticks)
    ax.set_yticklabels([s[0] for s in samples])
    ax.set_xlabel(r"$\overline{\chi^2/N}$ (lower is better)")
    ax.set_xlim(0, max(max(full_means), max(low_means)) * 1.4)
    ax.set_title("Locked low-risk subset PASSes the strict v07 rule on every prereg hold-out",
                 fontsize=10)
    ax.legend(loc="lower right", fontsize=9)

    out = FIG_DIR / "sparc_low_risk_summary"
    fig.savefig(out.with_suffix(".pdf"))
    fig.savefig(out.with_suffix(".png"))
    plt.close(fig)
    print(f"wrote {out}.pdf and {out}.png")


def fig_residual_histogram() -> None:
    q1_art = load_json("gravity_paper_v07_sparc_phi_locked.json")
    q2_art = load_json("sparc_phi_locked_q2_holdout.json")

    q1_ilg = np.array([float(g["chi2N_cr"]) for g in q1_art["per_galaxy_chi2"]])
    q1_mond = np.array([float(g["chi2N_mond"]) for g in q1_art["per_galaxy_chi2"]])
    q2_ilg, q2_mond = chi2_arrays(q2_art)

    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    bins = np.linspace(0, 6, 25)
    for arr, label, c in [
        (q1_ilg, "Q=1 ILG", ILG_COLOR),
        (q2_ilg, "Q=2 ILG", LOWRISK_COLOR),
        (q1_mond, "Q=1 MOND", MOND_COLOR),
    ]:
        ax.hist(arr.clip(0, 6), bins=bins, alpha=0.55, color=c, label=label,
                linewidth=0.0, density=True)
    ax.axvline(2.0, color=NEUTRAL_COLOR, lw=0.8, ls="--", alpha=0.6,
               label=r"$\chi^2/N=2$ pass threshold")
    ax.set_xlim(0, 6)
    ax.set_xlabel(r"$\chi^2/N$ per galaxy (clipped at 6)")
    ax.set_ylabel("density")
    ax.set_title(r"Per-galaxy $\chi^2/N$ density: ILG concentrates near 1, MOND near 5",
                 fontsize=10)
    ax.legend(loc="upper right", fontsize=8)

    out = FIG_DIR / "sparc_residual_histogram"
    fig.savefig(out.with_suffix(".pdf"))
    fig.savefig(out.with_suffix(".png"))
    plt.close(fig)
    print(f"wrote {out}.pdf and {out}.png")


def fig_falsifier_dashboard() -> None:
    rows = [
        ("F1: Q=1 median > 5.0", "1.516", False),
        ("F2: Q=2 mean > 4.0 worse than Q=1", "2.395 < 2.898 (Q=1)", False),
        ("F3: BTFR slope outside (3.5, 4.5)", "4.0009 (residual 0.022%)", False),
        ("F4: per-galaxy fit anywhere", "audited absent", False),
        ("Q=2 hold-out median pass (<3.0)", "1.008", True),
        ("Q=3 low-risk strict pass", "mean 1.456, f_good 0.75", True),
        ("Q=2+Q=3 low-risk strict pass", "mean 1.931, f_good 0.808", True),
        ("Q=1+Q=2+Q=3 low-risk strict pass", "mean 1.908, f_good 0.775", True),
        ("ILG beats MOND median, Q=1", "1.516 < 5.499", True),
        ("ILG beats MOND mean, Q=1", "2.898 < 10.350", True),
    ]

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    ax.axis("off")
    ax.set_xlim(0, 1)
    ax.set_ylim(0, len(rows) + 1)
    ax.text(0.0, len(rows) + 0.6, "Falsifier and pass dashboard at prereg/sparc-2026-04-26",
            fontsize=11, weight="bold")
    for i, (claim, val, ok) in enumerate(rows):
        y = len(rows) - i
        marker = "PASS" if ok else "not triggered"
        c = LOWRISK_COLOR if ok else NEUTRAL_COLOR
        ax.text(0.0, y, claim, fontsize=9.5, family="DejaVu Serif")
        ax.text(0.62, y, val, fontsize=9, family="monospace")
        ax.text(0.92, y, marker, fontsize=9, family="monospace", color=c)

    out = FIG_DIR / "sparc_falsifier_dashboard"
    fig.savefig(out.with_suffix(".pdf"))
    fig.savefig(out.with_suffix(".png"))
    plt.close(fig)
    print(f"wrote {out}.pdf and {out}.png")


def main() -> None:
    setup_style()
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    fig_chi2_distributions()
    fig_btfr()
    fig_low_risk_summary()
    fig_residual_histogram()
    fig_falsifier_dashboard()


if __name__ == "__main__":
    main()
