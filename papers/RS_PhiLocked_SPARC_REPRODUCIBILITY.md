# Reproducing the phi-locked SPARC paper

This repository contains the paper, scripts, generated figures, and frozen JSON artifacts for:

`A φ-Locked Information-Limited Gravity Test on SPARC: Preregistered, Zero Per-Galaxy Parameters`

Primary files:

- `papers/RS_PhiLocked_SPARC.tex`
- `papers/RS_PhiLocked_SPARC.pdf`
- `papers/RS_PhiLocked_SPARC_Prereg.md`
- `papers/figures/sparc_*.pdf`
- `papers/figures/sparc_*.png`
- `scripts/analysis/sparc_*.py`
- `artifacts/sparc_*.json`

The JSON artifacts are the frozen numerical basis of the paper. The paper’s numerical claims are read from those artifacts.

To regenerate the analysis artifacts, the SPARC catalog and rotation-curve files must be present in the same layout used by the private working repository:

```text
external/gravity/legacy/archives/snapshot-20250816-182339-tree/history/SPARC_Lelli2016c.mrt.txt
external/gravity/active/data/Rotmod_LTG/*_rotmod.dat
```

The raw SPARC data are public, but they are not bundled here. The generated JSON artifacts are bundled so the paper remains auditable even without the raw rotation-curve files.

Build the PDF from this repository with:

```bash
cd papers
pdflatex -interaction=nonstopmode -halt-on-error RS_PhiLocked_SPARC.tex
pdflatex -interaction=nonstopmode -halt-on-error RS_PhiLocked_SPARC.tex
```

The cited reproducibility tag in the private working tree is:

```text
prereg/sparc-2026-04-26
paper/sparc-v1-2026-04-27
```
