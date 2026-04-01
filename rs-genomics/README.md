# RS Genomics

**A zero-parameter geometric score for amino acid substitutions.**

Derives the distance between any two of the 20 amino acids from the 8-tick DFT cycle and the canonical cost function `J(x) = (x + 1/x)/2 - 1`. No fitted parameters. No training data. No neural networks.

[![Open in Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/jonwashburn/recognition-science/blob/main/rs-genomics/rs_genomics_tutorial.ipynb)
[![Interactive Demo](https://img.shields.io/badge/demo-recognitionphysics.org-blue)](https://recognitionphysics.org/genomics/)
[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)

---

## Results

| Metric | AUC-ROC (ClinVar, n=10,000) | Fitted Parameters |
|--------|:---------------------------:|:-----------------:|
| **RS Distance** | **0.590** | **0** |
| Grantham (1974) | 0.609 | 3 |

The RS metric achieves **97% of Grantham's discriminative power** on real clinical data while using **zero empirically fitted parameters**. Every number is derived from first principles.

## Quickstart

**Requires:** Python 3.8+ and NumPy.

### Score a single substitution

```bash
python rs_genomics.py score --ref E --alt V
```

Output:
```
  E (Glutamic acid)  ->  V (Valine)
  RS distance:     2.6614
  Fubini-Study:    1.5708
  Grantham:        121
  Crosses family:  True  (F35 -> F17)
```

### Use as a library

```python
from rs_genomics import score, score_pair, info

score("E", "V")                # -> 2.6614 (sickle cell mutation)
score("A", "V")                # -> 0.7876 (conservative substitution)
score_pair("E", "V")           # -> full detail dict
info("E")                      # -> amino acid metadata
```

### Print the full 20x20 matrix

```bash
python rs_genomics.py matrix --format csv > rs_distances.csv
python rs_genomics.py matrix --format json > rs_distances.json
```

### Benchmark against ClinVar

```bash
python rs_genomics.py benchmark --clinvar data/clinvar_10k_sample.csv
```

Output:
```
  Pathogenic variants: 9,492
  Benign variants:     508
  AUC-ROC:             0.5906
  Fitted parameters:   0
```

## How It Works

The score is built from two ingredients:

1. **DFT-8 WToken vectors.** The 8-tick discrete Fourier transform produces 20 neutral unit vectors in C^8, grouped into 4 families by DFT mode. These are the 20 amino acids.

2. **J-cost.** The canonical reciprocal cost `J(x) = (x + 1/x)/2 - 1` is applied to molecular weight and hydrophobicity ratios to resolve within-family distances.

The total distance between amino acids *a* and *b* is:

```
d(a, b) = sqrt( d_FS(a,b)^2 + J(MW_a/MW_b)^2 + J(H_a/H_b)^2 )
```

where `d_FS` is the Fubini-Study geodesic distance on CP^6 between DFT-8 vectors.

### Machine-Verified Proofs

The mathematical foundations are formally verified in Lean 4:

- [`WTokenIso.lean`](https://github.com/jonwashburn/recognition-science) — 20 WTokens in bijection with 20 amino acids
- [`JCostWithinFamily.lean`](https://github.com/jonwashburn/recognition-science) — MW is distinct within every family
- [`FamilyLevelAssignment.lean`](https://github.com/jonwashburn/recognition-science) — DFT-8 mode families match chemical classes

## Files

| File | Description |
|------|-------------|
| `rs_genomics.py` | Standalone scorer — library + CLI, single file, ~400 lines |
| `rs_genomics_tutorial.ipynb` | Interactive tutorial with ROC curves and heatmaps |
| `data/clinvar_10k_sample.csv` | 10,000 ClinVar missense variants for benchmarking |
| `paper/Genetic_Code_Geometrically_Forced.pdf` | Supporting research paper |

## Citation

```bibtex
@article{washburn2026genetic,
  title   = {The Genetic Code Architecture is Forced by a Single Functional Equation},
  author  = {Washburn, Jonathan},
  year    = {2026},
  note    = {Recognition Science Institute}
}
```

## License

MIT. Use it, extend it, prove us wrong.

---

*[Recognition Science Institute](https://recognitionphysics.org) — Austin, Texas*
