## IndisputableMonolith

Canonical framework library for the Recognition Science Lean 4 formalization.

This is the framework name used in the submitted paper:

> Pardo-Guerra, S., Simons, M., Thapa, A., Washburn, J., and Werner, B.
> *Coherent Comparison Costs from the d'Alembert Composition Law:
> Discrete Ledger Structure with a Lean 4 Formalization.*

It contains the cost functional, constants, observable-payload types,
structural certification, and bridge modules.

The `RecognitionScience/` tree extends this library with the forcing chain
(T0–T8), mass derivations, gravity, numerics, and verification certificates.
Both libraries are part of one framework; `lake build` compiles both.
