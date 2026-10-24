# Algebraic tokenization — Lean 4 formalization

Machine-checked formalization (Lean 4 + Mathlib) of the paper
*Algebraic tokenization and the quasitopos of regular heaps* (Wuming Pan, V6, prepared for Applied Categorical Structures).

The formal proof sources are those of commit `c9955f7`. This README clarifies their scope for the reorganized V6 manuscript; it does not change the proof code. Source comments retain V5 section numbers. The V6 correspondence is given in its Appendix E.

The development formalizes the core categorical constructions and representation results, including the regular-heap quasitopos theorem, the pullback/dependent-product adjunction, and the strong-subobject classifier. The project source contains no `sorry` or additional axiom declarations. The proofs use classical mathematics over Lean and Mathlib.

## Verification scope

- **Structural results:** `AT.mainTheorem` packages finite limits, finite colimits, local cartesian closure and a strong-subobject classifier. The corresponding constructions and regularity proofs are formalized. Principal relational and concrete representation results are also included.
- **Classical decidability statements:** `AT.RegTS.hom_decidable` and `AT.RegTS.usesShapes_decidable` prove `Nonempty (Decidable P)` using classical logic. Such a proposition can be inhabited classically for any `P`; these declarations do not verify executable decision algorithms. The failure-language equivalence and regularity are proved separately.
- **Finite search:** `AT.csp_decidable` gives a `Decidable` implementation under explicit finite-type, equality and relation-membership decidability assumptions. No complexity bound is certified by that declaration.
- **Outside the reported verification:** executable automaton emptiness procedures, an end-to-end executable implementation of the categorical constructions, polynomial/PSPACE/NP bounds, and complexity reductions. Those claims are argued in the paper using the cited results.

A successful build checks the encoded statements. It does not establish that every prose assertion in the manuscript has been formalized. See V6 Section 8 and Appendix E for the exact correspondence and exclusions.

## Build

```sh
# install elan (Lean version manager) if needed: https://github.com/leanprover/elan
lake exe cache get   # download Mathlib oleans
lake build
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib v4.35.0 (pinned in `lake-manifest.json`).

## Module map (V5 source numbering)

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
