# RS-Fold

**Glass-box protein folding on the phi-lattice.**

Every geometric parameter derived from the golden ratio. Zero training data. Zero free parameters.
Machine-verified in Lean 4.

## Install

```bash
pip install rsfold
```

## Usage

### Command line

```bash
# Fold a sequence
rsfold fold --sequence NLYIQWLKDGGPSSGRPPPS --output result.pdb

# Run benchmark suite
rsfold benchmark --output results.json
```

### Python API

```python
from rsfold import fold

result = fold("NLYIQWLKDGGPSSGRPPPS", iterations=2000)
print(f"Energy: {result.energy:.1f}")
print(f"Rg: {result.rg:.2f} A")
print(f"Contacts: {len(result.contacts)}")
```

## What this is

RS-Fold is a first-principles protein folding engine where:

- **CA-CA backbone distance** = phi^2 x 1.47 A = 3.85 A
- **Helix i->i+4 distance** = phi x backbone = 6.23 A
- **Beta-sheet interstrand** = sqrt(phi) x backbone = 4.90 A
- **Contact budget** = N / phi^2 (about 38% of possible contacts)
- **Rg target** = (N/phi)^(1/3) x backbone

All from phi = (1 + sqrt(5)) / 2. Nothing fitted.

## What this is not

A replacement for AlphaFold in production structure prediction. AF achieves
~1 A RMSD using deep learning on evolutionary data. RS-Fold achieves ~8-16 A
from pure physics. The value is the glass-box mechanism, not the accuracy.

## Benchmarks

| Protein | PDB | Size | RMSD | Rg Error |
|---------|-----|------|------|----------|
| Trp-cage | 1L2Y | 20 | 7.83 A | 1.6% |
| Villin HP36 | 1VII | 36 | 8.79 A | 0.5% |
| BBA5 | 1T8J | 22 | 7.77 A | 10.3% |

## Web demo

Try it in your browser: [recognition.physics.org/fold](https://recognition.physics.org/fold)

## Lean proofs

The geometric derivation chain is machine-verified:
[IndisputableMonolith/ProteinFolding/](https://github.com/jonwashburn/recognition-science)

## License

MIT
