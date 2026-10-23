# Algebraic tokenization — Lean 4 formalization

Machine-checked formalization (Lean 4 + Mathlib) of the paper
*Algebraic tokenization: fullness, symmetry, and effective presentations* (Wuming Pan).

All results in the paper are formalized with **no `sorry`** and no extra axioms beyond
Mathlib's standard `propext`, `Classical.choice`, `Quot.sound`.

## Build

```sh
# install elan (Lean version manager) if needed: https://github.com/leanprover/elan
lake exe cache get   # download Mathlib oleans
lake build
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib v4.35.0 (pinned in `lake-manifest.json`).

## Module map

| Module | Paper |
|---|---|
| `AT/Basic.lean` | §2.1 words, token classes, the category TS_E |
| `AT/Shape.lean` | §2.2 shape decomposition, Thm 2.4, finite limits |
| `AT/Signature.lean` | §2.3, §3 algebraic signatures and `Rep` |
| `AT/Slice.lean` | §3 slices, subterminals, used shapes |
| `AT/Fullness.lean` | §4 concrete fullness, finite interpolation |
| `AT/Regular/Defs.lean` | §5.2 regular heaps, RegTS, failure languages |
| `AT/Regular/Closure.lean` | §5.3 finite (co)limits, function objects |
| `AT/Regular/Quasitopos.lean` | §5.4 dependent products, strong subobjects, quasitopos theorem |
| `AT/Regular/Corollaries.lean` | §5 corollaries |
| `AT/Regular/Tree.lean` | §5.5–5.6 nested terms, protocol format |
| `AT/Relabel.lean` | §6 relabeling, release, naming |
| `AT/Symmetry.lean` | §7 sorted parameters, symmetry control, finite fields |
| `AT/CSP.lean` | §8 polymorphisms and CSP |
| `AT/Sequence.lean` | §9 sequence interfaces |
