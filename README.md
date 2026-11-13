# Lean 4 exercises

My work as I learn [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4). This is a learning log, so it is a work in progress.

## Contents

| File | What it covers |
| --- | --- |
| `Exercises.lean` | First warm-up problems: propositional logic, algebra with `ring`/`linarith`, divisibility and parity, sets, functions, induction |
| `Exercises2.lean` | [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/), chapter 2 (Basics): calculating with `rw`, proving identities in algebraic structures, using theorems and lemmas, `apply`, facts about algebraic structures |
| `Exercises3.lean` | *Mathematics in Lean*, chapter 3 (Logic): implication and ∀, the existential quantifier, negation |

Exercises still marked `sorry` are ones I haven't finished yet.

## Building

You need [elan](https://github.com/leanprover/elan) installed. Then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

CI runs `lake build` on every push to check that all the proofs compile.
