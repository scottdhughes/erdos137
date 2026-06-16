# Erdős Problem #137: powerful products of consecutive integers

Lean 4 / Mathlib formalization for Erdős Problem #137 (see erdosproblems.com/137), by Scott D. Hughes.

A number `N` is **powerful** if `p ∣ N ⟹ p² ∣ N`. Erdős Problem #137 (Erdős–Selfridge) asks
whether the product of `k ≥ 3` consecutive integers `F(k,n) = n(n+1)⋯(n+k-1)` can be powerful for
infinitely many `n` (for `k = 2`, `n(n+1)` is powerful infinitely often). It is **open**.

This repository formalizes the **abc-conditional** finiteness results, in each case isolating the
genuine abc input as a single explicit hypothesis and proving everything else outright (zero
`sorry`, no `native_decide`, only `{propext, Classical.choice, Quot.sound}`). Five result modules:

## `Erdos137/Finiteness.lean` — per-fixed-`k` finiteness (Granville–Langevin route)

Under `RadLB k` (the abc-conditional radical bound `rad(F(k,n)) ≫ n^{k-1-ε}`, taken as a
hypothesis), `F(k,n)` is powerful for only finitely many `n`, for each fixed `k ≥ 3`.

| Theorem | Statement |
|---|---|
| `lemma_star` | unconditional `rad m ^ 2 * B2 m ≤ m ^ 2` |
| `powerful_rad_sq_le` | a powerful `N ≠ 0` satisfies `rad N ^ 2 ≤ N` |
| `erdos137_eventually_not_powerful` | `k ≥ 3`, `RadLB k` ⟹ `F k n` not powerful for all large `n` |
| `erdos137_finite` | `k ≥ 3`, `RadLB k` ⟹ `{n ≥ 1 : F k n powerful}` finite |

## `Erdos137/JointFiniteness.lean` — the triple-tiling route, threshold `n > k^6`

The triple tiling of `F` and its radical-of-product decomposition, with the cross-block prime
**overlap proved** to satisfy `W ≤ k^k` (via `W ∣ k!`, Legendre — `W_le_pow`). The only hypothesis
is `BlockRadLB`, the abc block radical bound `(F k n)^{2/3} ≤ ∏ rad over triples`.

| Theorem | Statement |
|---|---|
| `rad_triples_decomp` | `∏_j rad(F 3 (n+3j)) = rad(B k n) · W k n` (proved) |
| `W_le_pow` | `W k n ≤ k^k` (proved, Legendre) |
| `not_powerful_of_large` | `BlockRadLB → 3 ≤ k → k^6 < n → ¬ Powerful (F k n)` |
| `not_powerful_finite` | per-`k` finiteness via the `n > k^6` threshold |

## `Erdos137/SmoothRefinement.lean` — the smooth-part refinement, sharpened to `n > k^{3+o(1)}`

The crude `rad(F)² ≤ F` is wasteful: the `k`-smooth part `S = ∏_{p<k} p^{v_p(F)}` of a powerful
`F` is itself very powerful (`S ≥ (k!)^{1-o(1)}`, while `rad(S) ≤ ∏_{p<k} p`). This gives the
**proved** refinement `rad(F)² · L ≤ F · P²` (`P` = primorial of `k`, `L = ∏_{p<k} p^{⌊k/p⌋}`),
i.e. `rad(F)² ≤ (P²/L)·F`.

| Theorem | Statement |
|---|---|
| `smooth_refinement` | powerful `F` ⟹ `rad(F k n)² · L k ≤ F k n · P k²` (proved) |
| `master_ineq` | `BlockRadLB` ⟹ `n^k · L^3 ≤ (k^{2k})^3 · P^6` (the crude `n^k ≤ k^{6k}` plus the `L^3` smooth gain) |
| `not_powerful_of_large'` | `BlockRadLB → 3 ≤ k → (k^{2k})^3·P^6 < n^k·L^3 → ¬ Powerful (F k n)` |
| `not_powerful_finite'` | per-`k` finiteness via the sharpened threshold |

The headline is stated in the **exact, fully-proved integer form** `(k^{2k})^3·P^6 < n^k·L^3`.
Substituting the Mertens lower bound `log L = k log k − O(k)` (and `P ≤ 4^k`) turns it into
`n > k^{3+o(1)}`, cubically below the crude `k^6`. That Mertens lower bound on `L` is **not in
Mathlib and is not formalized here**, so the repository carries the gain in the parametric form and
the `k^{3+o(1)}` reading is the pen-and-paper consequence.

## `Erdos137/TaoPoint.lean` — the elementary "very bad interval" structure

The deterministic core of Tao's *very bad intervals* (a block `[n,n+k-1]` whose product is
powerful), **unconditional** and purely valuation-theoretic. A prime `p ≥ k` divides at most one
of the `k` factors (two factors differ by `< k`), so in a very bad block all of `v_p(F)` comes
from that single factor and powerfulness squares it — and a prime `p > k` that *equals* a factor
cannot occur. The last lemma is the elementary step that pairs with a Baker–Harman–Pintz
prime-in-short-interval input.

| Theorem | Statement |
|---|---|
| `VeryBad k n` | `Powerful (F k n)` — Tao's very bad interval |
| `prime_dvd_two_terms_eq` | a prime `p ≥ k` divides at most one block factor |
| `veryBad_large_prime_sq` | very bad + `p ≥ k`, `p ∣ n+i` ⟹ `p² ∣ n+i` |
| `prime_in_block_not_powerful` | a prime `p > k` that is a block factor ⟹ `¬ Powerful (F k n)` |

Tao's analytic density theorem (`O(x^{2/5+o(1)})`) and his two-term linear-relation extraction
are **not** formalized — only the elementary uniqueness/valuation facts above.

## `Erdos137/SpliceFiniteness.lean` — the quintic per-`k` bound and the abstract splice machine

The **quintic** block route (`g = 5`, ingredient `4/5 > 2/3`) and an honest separation of two distinct
outputs. The single analytic input is `BlockRadLB5`, the tail-absorbed quintic block radical bound
`(F k n)^{4/5} ≤ ∏ rad over the ⌊k/5⌋ quintic blocks` — a normalized hypothesis guarded by `5 ≤ k`
(for `k < 5` there are no quintic blocks). From it alone, `powerful_bound_g5` gives the explicit
`Powerful (F k n) → n ≤ Msplice k`, hence `g5_finiteness` (**per-`k`** finiteness, for each fixed
`k ≥ 5`). Separately, `abstract_splice_no_counterexamples` is a range-splice **template**: parametric
in `Mid`/`High` predicates, it concludes `¬ Powerful (F k n)` from a `CoversAll` decomposition, a
**ranged** prime-in-block input on `Mid`, and a non-powerfulness input on `High` — keeping
Baker–Harman–Pintz, Mertens, and the exact exponents strictly external.

| Theorem | Statement |
|---|---|
| `W5_le_pow` | `W5 k n ≤ k^k` (proved, Legendre — the quintic overlap) |
| `master_ineq5` | `BlockRadLB5 → 5 ≤ k → Powerful → n^{3k}·L^5 ≤ (k^{2k})^5·P^{10}` |
| `not_powerful_g5` | `BlockRadLB5 → 5 ≤ k → (k^{2k})^5·P^{10} < n^{3k}·L^5 → ¬ Powerful (F k n)` |
| `powerful_bound_g5` | `BlockRadLB5 → 5 ≤ k → Powerful (F k n) → n ≤ Msplice k` (reusable core) |
| `g5_finiteness` | `BlockRadLB5 → 5 ≤ k → {n ≥ 1 : F k n powerful}` finite (per-`k`) |
| `upper_half_prime_not_powerful` | `n ≤ k → ¬ Powerful (F k n)` (**unconditional**, Bertrand) |
| `prime_range_not_powerful` | `PrimeInBlockOnRange Range → Range k n → ¬ Powerful (F k n)` |
| `abstract_splice_no_counterexamples` | `CoversAll Mid High` + ranged prime on `Mid` + non-powerful on `High` ⟹ `¬ Powerful` for all `(k,n)` |

The intended Pandey-free **no-gap** splice is an *asymptotic* reading of the abstract template:
`Mid` = the Baker–Harman–Pintz range `k < n ≤ k^{40/21−o(1)}`, `High` = the Mertens-sharpened quintic
range `n > k^{5/3+o(1)}`; since `5/3 < 40/21` the ranges overlap for all large `k` (with a finite
exceptional range and `k = 3,4` handled by the triple route). BHP, Mertens, and that asymptotic
coverage are **not** formalized — they enter only as the external premises of the splice theorem.

## What is and is not formalized

- **Proved (standard axioms only):** the radical decompositions, `W ≤ k^k` and `W5 ≤ k^k`, the
  smooth refinement `rad(F)²·L ≤ F·P²`, the quintic per-`k` bound (`powerful_bound_g5`,
  `g5_finiteness`) and the abstract range-splice template (`abstract_splice_no_counterexamples`), the
  elementary very-bad-interval lemmas (`TaoPoint`), and all the finiteness deductions.
  `Erdos137/AxiomAudit.lean` prints the footprint of every theorem above.
- **Hypotheses (the genuine, abc-conditional inputs, not formalized):** `RadLB` / `BlockRadLB` /
  `BlockRadLB5` (the last is the normalized, tail-absorbed quintic block bound, guarded `5 ≤ k`).
  abc itself is not formalized.
- **Not formalized:** the Mertens lower bound on `L` (so the sharpened threshold is parametric,
  with `k^{3+o(1)}` as its consequence); Tao's analytic density theorem and his two-term
  linear-relation extraction; the asymptotic `5/3 < 40/21` range coverage of the quintic splice
  (carried as the `CoversAll`/`High` premises of `abstract_splice_no_counterexamples`); and any
  unconditional input (e.g. Baker–Harman–Pintz, Pandey) used in the accompanying discussion.

## Verifying

```sh
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.28.0`, Mathlib pinned in `lake-manifest.json`; the build prints the
axiom report from `Erdos137/AxiomAudit.lean`.

## Attribution / related work

The finiteness under abc is a **known** consequence of the Granville–Langevin radical lower bound
(Langevin; A. Granville, [*ABC allows us to count squarefrees*](https://doi.org/10.1155/S1073792898000592),
IMRN 1998), discussed by T. N. Shorey and R. Tijdeman,
[*Arithmetic properties of blocks of consecutive integers*](https://arxiv.org/abs/1612.05438)
(2016, §8.1), with sharper power-free-part bounds due to B. M. M. de Weger and C. E. van de
Woestijne, *On the power-free parts of consecutive integers*, Acta Arith. 90 (1999), 387–395. The
problem is treated in T. Tao, *Products of consecutive integers with unusual anatomy*,
[arXiv:2603.27990](https://arxiv.org/abs/2603.27990) (2026), which records that #137 is open. The
triple-tiling and smooth-refinement contributions here arose from the discussion at
erdosproblems.com/137.

## License

Apache-2.0.
