# A Lean proof of Bugeaud, Distribution Modulo One, Problem 10.5

This repository proves both statements of
[Problem 10.5 in Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_5.lean):

1. the lower bound on the limsup of the fractional parts; and
2. the stronger “moreover” statement, which places a cluster point in every
   interval of the prescribed length.

For every real number field `K` and every `ε > 0`, the proof constructs one
positive lacunary sequence in `K` that works simultaneously for every real
`ξ ∉ K`.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbugeaud-10-5-lacunary%2Frefs%2Fheads%2Fmain%2Flean4web%2FBugeaud105Lean4Web.lean)

## Formal Conjectures targets

The `lean/` project imports the pinned Formal Conjectures file and proves
declarations whose types are taken directly from the two original targets:

```lean
theorem Bugeaud105.problem_10_5_moreover :
    type_of% Bugeaud05.problem_10_5_moreover

theorem Bugeaud105.problem_10_5 :
    type_of% Bugeaud05.problem_10_5
```

The original `sorry` proofs are never used.  The stronger theorem is proved
independently; the first theorem is then obtained from the repository's checked
implication `Bugeaud05.problem_10_5_of_moreover`.

The pinned environment is:

- Formal Conjectures commit `b86fdb9a8f2f83d2bb2b4281586705896c0c8208`;
- Lean `v4.33.1`; and
- mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

## Mathematical Explanation (AI generated)

Fix `ε > 0`.  Choose a positive natural number `Q > 1 / ε`, and put

```text
M = Q!,     J = 10M,
t(Jk + r) = (J + r) 2^k     for 0 ≤ r < J.
```

This is a positive integer sequence, hence it belongs to every intermediate
field of `ℝ/ℚ`.  Consecutive terms satisfy the strict lacunarity estimate with

```text
c = 1 + 1/(2J) > 1.
```

For every irrational `x`, the doubling orbit has arbitrarily late times `k`
with

```text
|x 2^k - round(x 2^k)| ≥ 1/4.
```

Apply this to `x = Mξ`.  Dirichlet approximation supplies a denominator
`1 ≤ q ≤ Q`; because `q ∣ Q!`, nearest-integer rounding then produces a
multiplier `j ∈ [J, 2J)` for which the fractional part of `j ξ 2^k` lies in any
requested interval `[a, a + ε] ⊆ [0, 1]`.  These hits occur arbitrarily late.
Compactness of the closed interval gives the required cluster point.

The construction actually proves the stronger statement for every intermediate
field of `ℝ/ℚ`; finite dimensionality is used only because it is present in the
Formal Conjectures target.

## Files

| Directory | Dependency | Purpose |
|---|---|---|
| `lean/` | Formal Conjectures at the pinned commit | Exact-type proof of both registered targets |
| `lean4web/` | mathlib `v4.33.1` only | One-file standalone proof for Lean4Web |

The `lean/` proof is split into small modules for the doubling-orbit escape,
factorial-window coverage, explicit lacunary sequence, cluster-point argument,
and exact compatibility with the target declarations.  The Lean4Web file
contains the same proof in one self-contained file.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both entry points end with `#print axioms`.  The expected output contains only
Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The proof files contain no `sorry`, `admit`, custom axiom, `native_decide`, or
unsafe theorem.

## Status boundary

The two statements are kernel checked in this repository.  At the pinned Formal
Conjectures commit, both declarations are still tagged `research open` and have
placeholder proofs.

## Sources

- [Bugeaud, *Distribution modulo one and Diophantine approximation*, Problem 10.5](https://staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf#page=233)
- [Formal Conjectures target file](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_5.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization and repository packaging were developed under the direction
of Kenta Kitamura ([KitaKen1 on GitHub](https://github.com/KitaKen1)), with
assistance from OpenAI's ChatGPT GPT-6 Astra and Codex GPT-6 Astra.
