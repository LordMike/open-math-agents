# Erdős 687 part iii: the R1 branch is false from `R1.H2.R1.H2` down

Target of this folder: step `Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H2.R1.H2`
(density amplification `Q^η → Q/√L`). Result: a disproof route, written as a compiled skeleton.

## What the step says, in plain terms

`S_min(M)` is the Ramanujan–Fejér sum over the divisors `d > D` of `Q = ∏_{p ≤ x} p`. By the lemmas
already in the chain (`ramanujan_fejer_identity`, `ramanujan_major_arc_bound`),

    S_min(M) = W(M) − L + O(L / log² L),

where `W(M) ≥ 0` is the Fejér-weighted count of `x`-rough integers in `(M, M + 2L)`, divided by
`∏_{p ≤ x}(1 − 1/p)`. Its mean over `M` is `L`. So `S_min(M) < −θL` means: the window after `M` has
fewer than a `(1 − θ)` share of the expected number of rough integers.

## Why the step is false

1. The conclusion of the step (at least `Q/√L` shifts with `S_min < −(θ/2)L`) fails for large `x`.
   This is Chebyshev plus the L² bound `∑_M S_min(M)² ≤ C·Q·L·log x`, which is the sibling step
   `…R1.H2.R1.H2.R1.H2.R1.H1` (proved in open PRs 7570 and 2766, CI green).
2. So the step holds only if its premise fails: fewer than `Q^η` shifts lie below `−(3θ/4)L`.
3. The premise is true for small `ε`. First step of the Erdős–Rankin construction: take
   `M ≡ 0` modulo every prime in `(w, x]` with `w = x^α`, and average over the residues modulo the
   primes `≤ w`. The survivors in a window of length `N = x^(1+ε)` are
   - `w`-smooth numbers: at most `2048·α²·N` (elementary, see Part C of the skeleton);
   - multiples of a prime `> x`: at most about `3εN`;

   and the averaging multiplies by `∏_{p ≤ w}(1 − 1/p) ≤ 1/log w ≈ 1/(α log x)`. The count is at most
   `(2048α + 6ε/α + o(1))·N/log x`, which is below `c·N/log x` for `α ≈ c/8192`, `ε ≈ cα/24`.
   The CRT subcube expansion (sibling step `…R1.H2.R1.H2.R1.H2.R1.H2.R1.H1`, open PR 3541, CI green)
   turns one such `M` into `Q^(c₁θε)` of them.

The constant (`c`, or `θ`) is chosen **before** `ε` in every statement of this branch. That is the
flaw: the share of rough integers a window of length `x^(1+ε)` can lose tends to 1 as `ε → 0`.

## How the Lean route uses this

No Fourier analysis is redone. The `main` theorems of the three merged reductions are imported and
chained:

    deep H2  --(R1.H2.R1.H2.R1.H2.R1.H2.R1.main, needs its H1 = CRT expansion, PR 3541)-->
    R1.H2.R1.H2.R1.H2.R1.H2  --(…R1.H2.R1.H2.R1.H2.R1.main, needs its H1 = L² bound, PR 7570)-->
    R1.H2.R1.H2.R1.H2        --(…R1.H2.R1.H2.R1.main, needs its H1 = Mertens, merged, @ivillar)-->
    R1.H2.R1.H2 = rough lower bound: ∃ c > 0, ∀ ε ∈ (0,1), eventually every block of length
                  ⌈x^(1+ε)⌉ has at least c·y/log x integers with no prime factor ≤ x.

The new mathematics is `E687Rankin.not_roughLB : ¬ OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H2`,
27 lemmas in four parts (A averaging and CRT, B multiples of large primes, C smooth numbers,
D assembly). It needs no unmerged work.

## Consequences for the tree

All 27 lemmas are now proved (Parts B, C and D2–D5 by two forks, the rest here), so `not_roughLB`
is a theorem. It disproves five steps. Every file below compiles in `fc/a8` with axioms
`propext, Classical.choice, Quot.sound`:

| step | file | extra input | state |
|---|---|---|---|
| `…parts.iii.R1.H2` (top) | `disproof_R1.H2.lean` | merged `R1.H1` (@santiemanuel) and Mertens (@ivillar), pasted | complete, no sorry |
| `…parts.iii.R1.H2.R1.H2` | `disproof_R1.H2.R1.H2.lean` | none | complete, no sorry |
| `…parts.iii.R1.H2.R1.H2.R1.H2` | `disproof_R1.H2.R1.H2.R1.H2.lean` | merged Mertens step, pasted | complete, no sorry |
| `…R1.H2.R1.H2.R1.H2.R1.H2` | `Skeleton.lean`, `E687Rankin.not_multiplicity` | L² step (PR 7570) | waits on the PR |
| `…R1.H2.R1.H2.R1.H2.R1.H2.R1.H2` (pool) | `Skeleton.lean`, `OMA.disproof` | L² step and CRT step (PR 3541) | waits on both PRs |

`check_deep_H2_with_unmerged_PRs.lean` is the pool disproof with the two PR proofs pasted in. It
compiles with no sorry, which shows the chain closes. It holds unmerged work of other people, so it
is a check only, not a file to submit.

The top step `R1.H2` is false, so the whole R1 reduction of part iii rests on a false hypothesis.
No other reduction of `R1.H2` can repair it. Only R2, R3 (and the open PR for R4) are live.

**The site has no way to submit this.** `tools/lint.py` accepts only
`theorem OMA.solution : <ns>.H<k>` for a step file; `OMA.disproof` is accepted for catalogue
problems only. So these files are evidence for an issue to the maintainer, not submissions. The
draft is in `ISSUE_DRAFT.md`.

## The other four pool steps (no route found)

- `R2.H1` (for infinitely many `j`, the primes up to `2·16^j` do not cover `[1, 64^j]`): this is
  `Y(x) < (x/2)^(3/2)` along a sequence. Open; the known bound is `x²/log² x`. Implied by the target.
- `R2.H2` (inside a long cover there is a block of length `√H` almost covered by the primes
  `≤ H^(1/3)`): true only vacuously as far as anyone can tell. A counterexample needs covers of
  length `≥ x^(1+ε)` for infinitely many `x`, which would refute the target; a proof needs the
  target (no such cover) for `ε < 1`, and for `ε ≥ 1` the known bound `Y(x) ≪ x²/log² x`. The
  conclusion would give `Y(2z) ≥ z^(3/2)`, so it cannot be proved by building the block either.
- `R3.H1` (a prime in `(n, n + n^(2/3)]` for large `n`): Ingham 1937. True, needs zero-density
  estimates; a known dead end for Mathlib.
- `R3.H2` (blocks starting at `b > L^(3/2)` in the first half of the period): the target itself
  minus a range that prime-gap theorems handle. Monotone in `ε`; for `ε ≥ 1` it follows from
  `Y(x) ≪ x²/log² x`. A split by Baker–Harman–Pintz (`b ≤ L^1.9`) would be a formal reduction with
  no content, so none was written.

No junk-value or quantifier slip was found in these four: natural division, `⌈·⌉₊` and the
`eventually` order are all used soundly there.

## Literature

The construction is the first step of Rankin 1938 / Erdős 1935 (large gaps between primes); see
Ford–Green–Konyagin–Maynard–Tao, Long gaps between primes (arXiv:1412.5029), section 2, where the
same choice `a_p = 0` for the middle primes leaves smooth numbers and multiples of large primes.
The smooth-number bound is the elementary log-weight argument iterated once (compare Tenenbaum,
Introduction to analytic and probabilistic number theory, III.5.1). These are cited by method; the
constants in the skeleton were derived here and checked numerically (`check.py`).
