# Erdős Problem #137: powerful products of consecutive integers

Lean 4 / Mathlib formalization for Erdős Problem #137 (see erdosproblems.com/137), by Scott D. Hughes.

A number `N` is **powerful** if `p ∣ N ⟹ p² ∣ N`. Erdős Problem #137 (Erdős–Selfridge) asks
whether the product of `k ≥ 3` consecutive integers `F(k,n) = n(n+1)⋯(n+k-1)` can be powerful for
infinitely many `n` (for `k = 2`, `n(n+1)` is powerful infinitely often). It is **open**.

This repository formalizes the **abc-conditional** finiteness results, in each case isolating the
genuine abc input as a single explicit hypothesis and proving everything else outright (zero
`sorry`, no `native_decide`, only `{propext, Classical.choice, Quot.sound}`). Nine result modules,
plus the shared `Base` layer and `AxiomAudit`.

**Module layering.** `Erdos137/Base.lean` holds the shared `g`-independent foundation (the
factorization/radical/Legendre helpers, the primorial `P` and Legendre layer `L`, and the smooth-part
refinement `rad(F)²·L ≤ F·P²`). `Erdos137/BlockFramework.lean` builds the generic `g`-block argument
on top of it. The concrete route modules below are then **literal instances**: `JointFiniteness` defines
`B`, `overlap`, `W` as `Bg 3`, `overlapg 3`, `Wg 3`, `SpliceFiniteness` defines `B5`, `overlap5`, `W5`
as the `g = 5` instances, and `QuarticCrude`/`SexticCrude` define `B4`/`B6` etc. as the `g = 4`/`g = 6`
instances, with their public lemmas re-derived as thin wrappers of the generic theorems (so the
per-`g` proofs live once, in `BlockFramework`/`Base`).

The **build/dependency order** is `Finiteness → Base → BlockFramework → JointFiniteness →
SmoothRefinement → TaoPoint → SpliceFiniteness → QuarticCrude → SexticCrude`. The module sections below are ordered
**pedagogically** (the concrete `g = 3, 5` routes first, then the unifying framework that subsumes
them), which is the reverse of the dependency direction: `BlockFramework`/`Base` are foundational, and
the concrete routes are their instances. A `(proved)` tag below means "a theorem, not a hypothesis";
for the `g = 3, 5` instance modules the proof itself lives upstream in `BlockFramework`/`Base`.

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
is `BlockRadLB`, the abc block radical bound `(F k n)^{2/3} ≤ ∏ rad over triples`. Here `B`, `overlap`,
`W` are the `g = 3` instances `Bg 3`, `overlapg 3`, `Wg 3`, and `W_le_pow`/`rad_triples_decomp`/
`not_powerful_of_large` are thin wrappers of `BlockFramework`'s `Wg_le_pow`/`rad_blocksg_decomp`/
`not_powerful_crude_g` (the proofs live there).

| Theorem | Statement |
|---|---|
| `rad_triples_decomp` | `∏_j rad(F 3 (n+3j)) = rad(B k n) · W k n` (proved) |
| `W_le_pow` | `W k n ≤ k^k` (proved, Legendre) |
| `not_powerful_of_large` | `BlockRadLB → 3 ≤ k → k^6 < n → ¬ Powerful (F k n)` |
| `not_powerful_finite` | per-`k` finiteness via the `n > k^6` threshold |

## `Erdos137/SmoothRefinement.lean` — the smooth-part refinement, sharpened to `n > k^{3+o(1)}`

The crude `rad(F)² ≤ F` is wasteful: the `k`-smooth part `S = ∏_{p<k} p^{v_p(F)}` of a powerful
`F` is itself very powerful (`S ≥ (k!)^{1-o(1)}`, while `rad(S) ≤ ∏_{p<k} p`). This yields the
refinement `rad(F)² · L ≤ F · P²` (`P` = primorial of `k`, `L = ∏_{p<k} p^{⌊k/p⌋}`), i.e.
`rad(F)² ≤ (P²/L)·F` — the lemma `smooth_refinement` and the `P`, `L` definitions live in `Base`
(they are `g`-independent). **This module** is the `g = 3` application: it combines that refinement
with the triple route to sharpen the threshold.

| Theorem | Statement |
|---|---|
| `smooth_refinement` (in `Base`) | powerful `F` ⟹ `rad(F k n)² · L k ≤ F k n · P k²` (proved) |
| `master_ineq` | `BlockRadLB` ⟹ `n^k · L^3 ≤ (k^{2k})^3 · P^6` (the `g = 3` instance of `master_ineq_g`) |
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
Baker–Harman–Pintz, Mertens, and the exact exponents strictly external. As in the triple route, `B5`,
`overlap5`, `W5` are the `g = 5` instances `Bg 5`, `overlapg 5`, `Wg 5`, and `W5_le_pow`/`master_ineq5`/
`g5_finiteness` are thin wrappers of `BlockFramework`'s generic theorems; the abstract splice machine is
unique to this module.

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

## `Erdos137/BlockFramework.lean` — the parametric `g`-block framework (unifying `g = 3, 5`)

The triple (`g = 3`) and quintic (`g = 5`) routes are the **same** argument at different block lengths.
This module factors that duplication into one parametric framework: the covered block product
`Bg g k n`, the overlap count `overlapg`, and the overlap factor `Wg`, with the uniform combinatorial
bounds `Wg ∣ k!` and `Wg ≤ k^k` (Legendre) proved **once**. Under the normalized tail-absorbed block
radical hypothesis `BlockRadLBg g` (guarded `g ≤ k`, for the same empty-product consistency reason),
it proves the smooth-refined **master inequality**, then the threshold and finiteness as corollaries.

| Theorem | Statement |
|---|---|
| `Wg_dvd_factorial` / `Wg_le_pow` | `Wg g k n ∣ k!`, `Wg g k n ≤ k^k` (proved, Legendre — the uniform overlap) |
| `master_ineq_g` | `BlockRadLBg g → 3 ≤ g → g ≤ k → Powerful → n^{(g-2)k}·L^g ≤ (k^{2k})^g·P^{2g}` |
| `not_powerful_g` | `BlockRadLBg g → Mg g k < n^{(g-2)k}·L^g → ¬ Powerful (F k n)` (sharp threshold) |
| `powerful_bound_g` | `BlockRadLBg g → Powerful → n ≤ Mg g k = (k^{2k})^g·P^{2g}` (coarse `L ≥ 1` collapse) |
| `g_finiteness` | `BlockRadLBg g → 3 ≤ g → g ≤ k → {n ≥ 1 : F k n powerful}` finite (per-`k`) |
| `master_ineq_crude_g` | `BlockRadLBg g → 3 ≤ g → g ≤ k → Powerful → n^{g-2} ≤ k^{2g}` (crude, no `L`/`P`) |
| `not_powerful_crude_g` | `BlockRadLBg g → k^{2g} < n^{g-2} → ¬ Powerful (F k n)` |
| `crude_g_finiteness` | `BlockRadLBg g → 3 ≤ g → g ≤ k → {n ≥ 1 : F k n powerful}` finite (crude) |

There are **two routes**. The **smooth** `master_ineq_g` carries the `L^g` factor and is sharper, but
its `k^{1+ε}` reading is gated behind unformalized Mertens (below). The **crude** `master_ineq_crude_g`
drops the smooth refinement (`rad(F)² ≤ F` in place of `rad(F)²·L ≤ F·P²`), giving the clean integer
law `n^{g-2} ≤ k^{2g}` with a **fully explicit** threshold `n > k^{2g/(g-2)}` — `g = 3 → k^6`,
`g = 4 → k^4`, `g = 6 → k^3` — no constants left implicit. The crude route trades the sharper exponent
for an honest explicit bound; `not_powerful_of_large` (g=3) is now its `g = 3` instance.

The master inequality specializes **exactly** to the recorded cases: `g = 3` gives `n^k·L^3 ≤
(k^{2k})^3·P^6` (the `SmoothRefinement` threshold) and `g = 5` gives `n^{3k}·L^5 ≤ (k^{2k})^5·P^{10}`
(the `SpliceFiniteness` threshold) — and definitionally `Bg 3 = B`, `Wg 3 = W`, `Bg 5 = B5`,
`Wg 5 = W5`, `Mg 5 = Msplice`, so the existing concrete code **is** the `g = 3, 5` instance.

There are two exponent readings, and they must not be conflated. With only the proved `L k ≥ 1`, the
master inequality gives the **coarse** `n > k^{2g/(g-2)+o(1)}`, whose exponent tends to `2` (toward
`k^{2+ε}`) as `g → ∞`. The `k^{1+ε}` reading appears **only** after the unformalized Mertens lower
bound `log L = k log k − O(k)`, which sharpens it to `n > k^{g/(g-2)+o(1)}` (exponent `→ 1`). The
`.Finite` wrapper deliberately uses the coarse explicit `n ≤ Mg g k`; the sharp exponent stays an
external asymptotic reading. This is not an unconditional improvement either: the abc/Langevin constant
packaged in `BlockRadLBg g` depends on fixed `g` — the known radical-method ceiling, not a uniform
growing-`g` theorem.

## `Erdos137/QuarticCrude.lean` — the quartic (`g = 4`) crude route, threshold `n > k^4`

The `g = 4` instance of the crude route, carried to its sharp explicit form. Under `BlockRadLB4` (the
reader-friendly `(F k n)^{3/4} ≤ ∏ rad` over quartic blocks, `blockRadLB4_iff`-bridged to
`BlockRadLBg 4`), the crude master inequality reads `n^2 ≤ k^8`, i.e. `n ≤ k^4`.

| Theorem | Statement |
|---|---|
| `not_powerful_of_large_g4` | `BlockRadLB4 → 4 ≤ k → k^4 < n → ¬ Powerful (F k n)` |
| `g4_crude_finiteness` | `BlockRadLB4 → 4 ≤ k → {n ≥ 1 : F k n powerful}` finite (all `n ≤ k^4`) |

The crude exponent is `2g/(g-2) = 2 + 4/(g-2)`, so `g = 4` is the **first (minimal)** block length for
which the crude threshold drops below the `k^5` squarefree ceiling, and it gives the clean integer
threshold `k^4`. Larger fixed block lengths give still smaller crude exponents — for example `g = 6`
gives `k^3` — but require correspondingly higher-degree block radical inputs (`g = 5` gives the
non-integer `k^{10/3}`). This `n > k^4` bound is the complementary high-`n` input for the usual
squarefree-counting reduction: combined with the low-range prime obstruction and Pandey's unconditional
squarefree short-interval count below `k^{5+δ}`
([arXiv:2401.13981](https://arxiv.org/abs/2401.13981)), it is the high-`n` part of the intended joint
`(n, k)` finiteness argument. Pandey's count is **not** formalized here.

## `Erdos137/SexticCrude.lean` — the sextic (`g = 6`) crude route, threshold `n > k^3`

The `g = 6` instance of the crude route, the **sharpest clean integer-exponent crude threshold this
route reaches**. Under `BlockRadLB6` (the `(F k n)^{5/6} ≤ ∏ rad` bound over sextic blocks,
`blockRadLB6_iff`-bridged to `BlockRadLBg 6`), the crude master inequality reads `n^4 ≤ k^12`, i.e.
`n ≤ k^3`.

| Theorem | Statement |
|---|---|
| `not_powerful_of_large_g6` | `BlockRadLB6 → 6 ≤ k → k^3 < n → ¬ Powerful (F k n)` |
| `g6_crude_finiteness` | `BlockRadLB6 → 6 ≤ k → {n ≥ 1 : F k n powerful}` finite (all `n ≤ k^3`) |

The crude exponent `2g/(g-2) = 2 + 4/(g-2)` is an integer exactly when `(g-2) ∣ 4`, i.e. precisely for
`g ∈ {3, 4, 6}` — giving `k^6`, `k^4`, `k^3`. So `g = 6` is the **last (largest) block length with an
integer crude exponent**, and `k^3` is the sharpest clean integer crude threshold: beyond `g = 6` the
crude exponent is non-integer and only decreases toward `k^2` as `g → ∞`. The gain over `g = 4` costs a
higher-degree block radical input (`BlockRadLB6`, with its `g`-dependent abc/Langevin constant — the
known radical-method ceiling). `k^3` stays below the `k^5` unconditional ceiling, so it too is a valid
high-`n` input for the squarefree-counting reduction.

## `Erdos137/SquarefreeCapacity.lean` — the deterministic squarefree-capacity reduction

The deterministic half of the squarefree-counting route, with **no** analytic number theory (no Pandey,
no Baker–Harman–Pintz, no Mertens). If `F k n` is powerful, then every squarefree term `n+i` in the
block has no prime factor `p ≥ k` — otherwise the `TaoPoint` large-prime uniqueness lemma
(`veryBad_large_prime_sq`) forces `p² ∣ n+i`, contradicting squarefreeness. So each squarefree term is
`(k-1)`-smooth, contributes valuation `≤ 1` at each `p < k`, and at most `⌊k/p⌋+1` block terms are
divisible by `p` (`Ioc_dvd_le`). Hence the product of the squarefree terms divides the small-prime
capacity `∏_{p<k} p^{⌊k/p⌋+1}`.

| Theorem | Statement |
|---|---|
| `sqfree_term_no_large_prime` | powerful block + squarefree `n+i` ⟹ no prime `p ≥ k` divides `n+i` |
| `powerful_sqfree_product_dvd_smooth_capacity` | `Powerful (F k n) → SqfreeBlockProduct k n ∣ SmoothCapacity k` |
| `powerful_sqfree_product_le_smooth_capacity` | `Powerful (F k n) → SqfreeBlockProduct k n ≤ SmoothCapacity k` |

Here `SqfreeBlockProduct k n = ∏_{i<k, n+i squarefree} (n+i)` and `SmoothCapacity k = ∏_{p<k} p^{⌊k/p⌋+1}`
(the `⌊k/p⌋+1` exponent, not a ceiling, is exactly what `Ioc_dvd_le` proves). This is the deterministic
companion to an **external** squarefree-counting theorem such as Pandey's: it converts "enough squarefree
terms in the block" into a contradiction with the capacity bound, **modulo** that count, which is not
formalized here.

## What is and is not formalized

- **Proved (standard axioms only):** the radical decompositions, the uniform overlap bound
  `Wg ≤ k^k` (with `W ≤ k^k`, `W5 ≤ k^k` its `g = 3, 5` instances), the smooth refinement
  `rad(F)²·L ≤ F·P²`, the parametric **smooth** master inequality `n^{(g-2)k}·L^g ≤ (k^{2k})^g·P^{2g}`
  (`master_ineq_g`) and the parametric **crude** master inequality `n^{g-2} ≤ k^{2g}`
  (`master_ineq_crude_g`), their per-`k` bounds/finiteness (`powerful_bound_g`, `g_finiteness`,
  `crude_g_finiteness`, and the sharp instances `not_powerful_of_large_g4` / `g4_crude_finiteness`
  (`k^4`) and `not_powerful_of_large_g6` / `g6_crude_finiteness` (`k^3`)), the
  abstract range-splice template (`abstract_splice_no_counterexamples`), the elementary
  very-bad-interval lemmas (`TaoPoint`), the deterministic squarefree-capacity reduction
  (`powerful_sqfree_product_dvd_smooth_capacity`), and all the finiteness deductions.
  `Erdos137/AxiomAudit.lean` prints the footprint of every theorem above.
- **Hypotheses (the genuine, abc-conditional inputs, not formalized):** `RadLB` / `BlockRadLB` /
  `BlockRadLB4` / `BlockRadLB5` / `BlockRadLB6` / `BlockRadLBg g` (the block bounds are the normalized,
  tail-absorbed forms, guarded `4 ≤ k` / `5 ≤ k` / `6 ≤ k` resp. `g ≤ k`). abc itself is not formalized;
  each enters as a premise, so none appears in any axiom footprint.
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
