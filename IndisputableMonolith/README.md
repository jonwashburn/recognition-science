## IndisputableMonolith

Internal support library for the Recognition Science Lean 4 formalization.

This library provides structural certification, observable-payload types
(`LeptonMassRatios`, `CkmMixingAngles`), and bridge modules. The canonical
public namespace is `RecognitionScience/`, which matches the artifact
analyzed in the submitted JAR paper:

> Simons, M. and Washburn, J.
> *Certificate-Based Verification of Derivation-Graph Structural Properties
> in Lean 4/Mathlib.*

Both libraries are part of one framework; `lake build` compiles both.
