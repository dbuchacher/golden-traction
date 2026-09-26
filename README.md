# golden-traction

[![Build and check axioms](https://github.com/dbuchacher/golden-traction/actions/workflows/build.yml/badge.svg)](https://github.com/dbuchacher/golden-traction/actions/workflows/build.yml)

Two projects that turned out to fit together:

- **Null Theory** ([Tristan Stevens, Zenodo](https://zenodo.org/records/20369503)) builds its framework from one
  combinatorial object, the Fibonacci substitution `σ : A ↦ AB, B ↦ A`, and the ring ℤ[φ] it generates.
- **Traction** ([sibarum/cott-lean](https://github.com/sibarum/cott-lean)) is a Lean 4 formalization of
  unreduced integer pairs `T(p, q)`, on which every quadratic ring is one product: read `T(p, q)` as
  `q + p·ω` and choose `ω² = a + b·ω`.

ℤ[φ] is the row `ω² = 1 + ω` of that family. This repository writes Null Theory's combinatorial core down on
traction's pairs and has Lean check it: 28 theorems in [`Golden.lean`](Golden.lean), built on cott-lean,
no `sorry`, only Lean's standard axioms (CI runs the check on every push).

It covers the combinatorial layer only: the substitution, its matrix, its parity and its conjugation. The
spectral and physical parts of Null Theory are out of scope here.

## Where this came from

This started as a thread on X. We pointed out that Null Theory reads `∅` two ways: as absence in Definition
2, and as a balance in Remark 216. Tristan replied:

> ∅ is the subset of all sets, so it's actually happening everywhere. That's why you have cosmic inflation
> universally. It's also why the big bang is pre-time and one point, infinitely dense. ∅ → {∅} is also
> pre-time, one point, infinitely dense.

This repository is our answer, written so Lean can check it. Two parts of it respond to that thread directly:

- **"Happening everywhere" is the stronger half.** If `∅` is a subset of every set, it is in every iterate
  too, not only before the first one. On the pairs, the empty word is fixed by `σ` at every depth
  (`σⁿ(ε) = ε`), and its count `T(0,0)` is the unit inside every count. So "happening everywhere" and
  "pre-time" pull against each other, and the checked statements side with the first: the bang is not before
  time, it is happening at every depth, now. See [The empty word is at every depth](#what-is-proved).
- **The substitution matrix has a second reading.** Read backward, `[[1,1],[1,0]]` becomes `[[0,1],[1,−1]]`,
  and the flip that Null Theory carries as a separate parity sits inside the step. That is the next section.

## One table, two ways to read it

Null Theory's substitution matrix reads the step forward. The same step read from the other end, with the
sign flipped, is a second table:

```
   forward (Null Theory)          backward (the flipped reading)

      ┌       ┐                      ┌        ┐
      │ 1   1 │                      │ 0    1 │
      │ 1   0 │                      │ 1   −1 │
      └       ┘                      └        ┘

   newer + older                  older − newer
   multiply by ω = φ              multiply by _1 = 1/φ
   det = −1                       det = −1
```

They are exact inverses, `[[1,1],[1,0]] · [[0,1],[1,−1]] = I` both ways round, so neither table loses anything
the other keeps. The backward one is the Fibonacci numbers with every other sign flipped:

```
n          0    1    2    3    4    5    6    7    8
F(n)       0    1    1    2    3    5    8   13   21      forward:  newer + older
G(n)       0   −1    1   −2    3   −5    8  −13   21      backward: older − newer

F(n) mod 3 0    1    1    2    0    2    2    1    0      home at 8
G(n) mod 3 0    2    1    1    0    1    2    2    0      home at 8
```

Checked in Lean:

```lean
theorem qmat_underOne : qmat 1 1 «_1» = !![0, 1; 1, -1]              -- the backward table is ×(1/φ)
theorem walker_mul_sigma : !![0, 1; 1, -1] * !![1, 1; 1, 0] = 1 ∧
                           !![1, 1; 1, 0] * !![0, 1; 1, -1] = 1      -- exact inverses
theorem step_back (x : T) : gtimes (gtimes x «ω») «_1» = x            -- forward then back, on every pair
theorem flipped_fib (n : ℕ) : (-1)^(n+2) * F(n+2) = (-1)^n * F(n) - (-1)^(n+1) * F(n+1)
theorem sigma_mod3_lap  : [[1,1],[1,0]]^8 = 1 ∧ [[1,1],[1,0]]^4 ≠ 1   -- over ZMod 3
theorem walker_mod3_lap : [[0,1],[1,-1]]^8 = 1 ∧ [[0,1],[1,-1]]^4 ≠ 1
```

(Statements abbreviated; the exact ones are in [`Golden.lean`](Golden.lean).)

What this says about the framework: Null Theory has the flip, but as a separate `ℤ/2` grading laid on top of
the step (its "Möbius parity", `det M = −1`). In the backward table the flip is inside the step itself.
Direction stops being a label on the step and becomes which end you read it from. The `det = −1` is exactly
why the backward walk stays on the integers. The backward reading was maxi's noticing.

## The dictionary

A word over {A, B} is counted as the pair `T(#A, #B)`. The letter `A` is `ω = T(1,0)` and `B` is
`0 = T(0,1)`, so counting a word is the mediant `⊕` of its letters.

| Null Theory | on traction pairs | theorem |
|---|---|---|
| the ring ℤ[φ], `φ² = φ + 1` | the row `qtimes 1 1` (discriminant 5) | `gtimes` |
| substitution matrix `M = [[1,1],[1,0]]` | multiplying by `ω`; `qmat 1 1 ω` is `M` | `qmat_omega` |
| `σ` acting on letter counts | the count of `σ(w)` is the count of `w` times `ω` | `counts_sigma` |
| `μ(x) = 1 + 1/x`, `x ≠ 0` (Theorem 18) | total: the word `B` (ratio `0/1`) steps to `A` (ratio `1/0`) | `sigma_B`, `step_zero` |
| Fibonacci counts of `σⁿ(A)` | `T(F(n+1), F(n))` | `counts_sigma_iterate` |
| Möbius parity, `det M = −1` | the norm of `ω` is `−1`, and the norm is multiplicative | `gnorm_omega`, `gnorm_gtimes` |
| Cassini | the norm of `σⁿ(A)`'s count is `(−1)ⁿ⁺¹` | `gnorm_counts_sigma_iterate`, `cassini` |
| Galois face `φ ↔ ψ` | a pair map; a pair times its flip lands on `T(0, N)` | `gconj`, `gtimes_gconj` |
| the seed `∅` | the empty word; its count is `0ω = T(0,0)`, traction's `0/0` | `counts_nil` |

## What is proved

**The substitution is a product.** Counting letters turns `σ` into multiplication by `ω` in the golden row,
for every word (`counts_sigma`), and the matrix of that multiplication is exactly `[[1,1],[1,0]]`
(`qmat_omega`). No ratio is ever formed, so no case is excluded. `μ(x) = 1 + 1/x` has to set `x ≠ 0` aside,
yet `σ` itself passes through that point: the word `B` has ratio `0/1` and `σ(B) = A` has ratio `1/0`. On the
pairs this is the step `0 ↦ ω`, with nothing to exclude (`step_zero`, `sigma_B`).

**Every iterate holds the earlier ones whole.**

```
n   σⁿ(A)            contains
0   A
1   AB               row 0
2   ABA              row 1 + row 0
3   ABAAB            row 2 + row 1
4   ABAABABA         row 3 + row 2
5   ABAABABAABAAB    row 4 + row 3
```

`σⁿ⁺²(A) = σⁿ⁺¹(A) ++ σⁿ(A)` for every `n` (`sigma_iterate_append`), and `M² = M + I` says the same thing on
the counts. Read this way, the infinite word is the one object and each `σⁿ` is a coarser read of it: depth
is resolution, not duration. Null Theory's heat-kernel time `T = φ⁻ⁿ` already works like that, as a depth.

**The parity is the norm of ω.** `N(q + pω) = q² + pq − p²`. `N(ω) = −1` and `N` is multiplicative, so the
counts of `σⁿ(A)` carry `(−1)ⁿ⁺¹` (`gnorm_counts_sigma_iterate`), which is Cassini's identity
(`cassini`). The determinant `−1` grading is one norm, read off one element.

**The Galois flip is a pair map.** `φ ↦ ψ` is `ω ↦ 1 − ω`, which is `T(p, q) ↦ T(−p, q + p)` on the pairs
(`gconj`). It undoes itself (`gconj_gconj`), and a pair times its flip lands on `T(0, N)`, the norm as a
pair (`gtimes_gconj`).

**Run backward, the step is multiplication by 1/φ.** See [One table, two ways to read it](#one-table-two-ways-to-read-it)
above (`qmat_underOne`, `walker_mul_sigma`, `step_back`, `flipped_fib`, `sigma_mod3_lap`, `walker_mod3_lap`).

**The empty word is at every depth.** `σⁿ(ε) = ε` for every `n` (`sigma_iterate_nil`). `ε` sits inside every
iterate, and its count, `0ω = T(0,0)`, is the unit inside every count (`nil_in_every_iterate`). Every golden
product it touches lands on it (`gtimes_zeroOmega`). So `∅` is not only before the first step; it is carried
through all of them. On the pairs `0/0` is a value, not a singularity.

## Two readings worth putting side by side

**Absence or balance.** Null Theory's Definition 2 identifies `(A, B) = (∅, {∅})` with `(0, 1)`, presence and
absence. Its Remark 216 then takes the most void-like measure to be the uniform `½, ½` one, "equilibrium …
every distinction equiprobable, no structure preferred": the void as a balance. In balanced ternary
`{−1, 0, +1}` that is what zero is, the point where the two signs cancel, and in traction `0ω` is exactly the
point every direction shares. The two readings pull in different directions, and it may be worth choosing
which one the framework stands on.

**Step in time, or depth held whole.**

| step-in-time reading | held-whole reading | where the first holds |
|---|---|---|
| `∅ → {∅}` is one event at the origin | the distinction is made at every read, at every depth | in the order marks are written |
| iteration `n` is step `n` | depth `n` of one word | when counting rewrites |
| the fixed point is a limit | the fixed point is the object; the iterates are reads of it | in the construction order |
| `T = φ⁻ⁿ` is a parameter | `T` is a depth (resolution) | in the spectral bookkeeping |

## Where else traction meets Null Theory

Traction's split-complex row `ω² = 1` is exact relativistic velocity addition: its zero divisors are the two
light lines, and light plus any velocity is light, as a theorem (`one_splitTimes`, `splitTimes_eq_zeroOmega_iff`
in cott-lean). So the invariance of `c` is a fact about that ring. Null Theory's substitution (discriminant 5)
and a Lorentz boost (discriminant 4) are both hyperbolic rows of the same family, each with two fixed
directions: the golden eigenlines for one, the light lines for the other. That is a likeness with no shared
reason shown yet, and it's offered as such. Traction gives the exact algebra of boosts; it does not give
Null Theory's emergence of Lorentz symmetry from the quasicrystal.

## Two offers

**State the selection rule in Lean.** Written as a Lean definition, the KFP selection rule would turn "the
catalogue is forced, zero freedom" into a statement Lean can check, and the pairs here are a ready carrier for
the `ℤ[φ]` addresses it acts on.

**Run a random-target control.** `p + qφ` is dense in the reals, so precision alone can't show how much choice
each fit had. [`scripts/random_targets.py`](scripts/random_targets.py) fits random numbers with the same form,
`φ^(p + qφ + s₁/φⁿ¹ + s₂/φⁿ²)`, with `|q| ≤ 2` and an approximation of the B-span depths: RMS 0.062%, worst
0.31%, 232 of 300 within 0.063%, next to the catalogue's 0.063% RMS. It skips the KFP rules, which narrow the
choice, so it is not a refutation. Running the real pipeline on shuffled or random targets and reporting the
hit rate would settle it, and if random targets fail where the physics passes, that is a much stronger result.

## Building

Lean `v4.33.0`, with Mathlib pulled in through cott-lean (pinned in `lakefile.toml`).

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` walks every declaration in `Golden` and fails on any axiom other than `propext`,
`Classical.choice` and `Quot.sound`, so a `sorry` or `native_decide` would fail it. It is adapted from
cott-lean's own check.

## Credits

The traction model and every lemma `Golden.lean` builds on are sibarum's
([cott-lean](https://github.com/sibarum/cott-lean)). The substitution, the ℤ[φ] framework and the questions
are Tristan Stevens' ([Null Theory](https://zenodo.org/records/20369503),
[Lorentz paper](https://zenodo.org/records/21565202)). Any error in putting them together is ours.
