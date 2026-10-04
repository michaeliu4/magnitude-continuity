# Magnitude continuity at finite sets

This standalone Lean 4 package contains the proof sources formalizing Theorem 1.1 of the associated manuscript, *Magnitude continuity at finite sets in finite-dimensional L1 subspaces*. The manuscript itself is not included here.

The default `Results` library imports only `Results.MagnitudeContinuity.Solution.Main`. It does not include the statement-only `Challenge.lean` module or any `sorry` placeholders.

## Scope

The selected declarations are:

- `Results.MagnitudeContinuity.main`
- `Results.MagnitudeContinuity.main_tendsto`
- `Results.MagnitudeContinuity.main_of_embedding`
- `Results.MagnitudeContinuity.main_of_L1`

The source formalization passed its Level 3 audit with coverage `full_assuming`. The first two declarations explicitly assume `Results.MagnitudeContinuity.MeckesEmbedding`, which states that every finite-dimensional positive-definite real normed space admits a linear isometry into `L1[0,1]`. The latter two declarations instead take the needed embedding data directly or specialize to an `L1` subspace.

## Build

The package pins Lean and Mathlib to `v4.32.1` and records the complete dependency revisions in `lake-manifest.json`.

Run these commands from the repository root:

```sh
lake exe cache get
lake build Results
lake env lean PrintAxioms.lean
```

`PROVENANCE.md` maps every copied proof source to its Git blob at protected source commit `b3da9c75451546c72845b58d74308222adb5f9ae`.

## Review boundary

Lean checks the declarations relative to Lean's kernel, Mathlib, and the explicit theorem hypotheses. This package does not establish the external embedding theorem, certify the manuscript's prose, or constitute journal peer review, publication, or acceptance of the mathematical claim.

## Rights

This repository makes no new license grant for the Lean sources. Lean and Mathlib are external dependencies with their own licenses.
