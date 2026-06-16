import Erdos137.Finiteness

namespace Erdos137

/-!
# Erdős Problem #137: per-`k` non-powerfulness via the triple tiling

`Erdos137/Finiteness.lean` formalizes the **per-fixed-`k`** conditional result: under the
Granville–Langevin radical lower bound `RadLB k` (a consequence of the abc conjecture, taken
as a hypothesis), for each fixed `k ≥ 3` the product `F k n = n(n+1)⋯(n+k-1)` is powerful for
only finitely many `n`.

This file formalizes the **triple-tiling** route (motivated by Will Sawin's comment at
erdosproblems.com/137). Under the block radical lower bound `BlockRadLB` (the genuine abc input,
applied to the cubic triples), for `k ≥ 3` and `n > k^6` the product `F k n` is **not powerful**
(`not_powerful_of_large`); hence, for each fixed `k`, `F k n` is powerful for only finitely many
`n` (`not_powerful_finite`).

## The argument

* Langevin/abc gives, for the squarefree cubic `g(x) = x(x+1)(x+2)`,
  `rad(m(m+1)(m+2)) ≫_ε m^{2-ε}`. Assembled over `⌊k/3⌋` consecutive triples this is
  `∏ rad over triples ≥ (F k n)^{2/3 - ε}` (taken as `BlockRadLB`, the genuine abc input).
* `rad(F k n) = (∏ rad over triples) / W`, where `W = ∏_{p} p^{overlap − 1}` is the over-count
  from primes appearing in more than one triple.
* Each triple is 3 consecutive integers, so the `⌊k/3⌋` triples span `≤ k` consecutive integers.
  A prime `p` divides at most `⌊k/p⌋ + 1` of them, hence `overlap k n p − 1 ≤ ⌊k/p⌋ ≤ v_p(k!)`
  (Legendre's `i = 1` term). Therefore **`W ∣ k!`**, so **`W ≤ k! ≤ k^k`** — proved here. On the
  log scale `log W = ∑_{p<k} ⌊k/p⌋ log p = k log k + O(k)` (the first Legendre layer of `k!`, by
  Mertens' first theorem `∑_{p<k} (log p)/p ∼ log k`), so `W` is `(F k n)^{o(1)}` only for `n`
  super-polynomial in `k`; for `n ≍ k^A` it is `(F k n)^{1/A + o(1)}`, and the triple (`g = 3`)
  route yields the threshold `n > k^6` rather than all `n`.
* `F k n ≥ n^k` (each of the `k` factors is `≥ n`) — proved here.
* Combine: `(F k n)^{2/3} ≤ rad(F k n) · W`, powerful ⟹ `rad(F k n)^2 ≤ F k n`, and `W ≤ k^k`,
  giving `(F k n)^{1/3} ≤ k^{2k}`. With `F k n ≥ n^k`: `n^{k/3} ≤ k^{2k} = (k^6)^{k/3}`, so
  `n ≤ k^6`. Thus `n > k^6` ⟹ `¬ Powerful (F k n)`.

## What is fully proved here (no `sorry`, only Mathlib's three axioms)

* `triples_prod_dvd`, `rad_triples_decomp`, `rad_triples_le` — the radical-of-product
  decomposition `∏_j rad(F 3 (n+3j)) = rad(B k n) · W k n` and its usable inequality.
* `Ioc_dvd_count` / `Ioc_dvd_le` — exact / bounded count of multiples of `p` in an interval.
* `overlap_le` : `overlap k n p ≤ ⌊k/p⌋ + 1` (the combinatorial overlap count).
* `div_le_factorization_factorial` : `⌊k/p⌋ ≤ v_p(k!)` (Legendre's `i = 1` term).
* `W_dvd_factorial` : `W k n ∣ k!`. `W_le_pow` : **`W k n ≤ k^k`** (the overlap bound).
* `pow_le_F` : `n^k ≤ F k n`.
* `not_powerful_of_large` : `BlockRadLB → 3 ≤ k → k^6 < n → ¬ Powerful (F k n)` — the headline.
* `not_powerful_finite` : `BlockRadLB → 3 ≤ k → {n | 1 ≤ n ∧ Powerful (F k n)}.Finite`.

## The boundary: what is hypothesized

The ONLY hypothesis is `BlockRadLB`: the assembled Langevin/abc radical lower bound
`(F k n)^{2/3} ≤ ∏ rad over triples`. This is the genuine, abc-conditional input (abc itself is
NOT formalized); it is stated in the `ε = 0`, `C = 1` extremal form, which yields exactly the
clean threshold `n > k^6` (the realistic Langevin bound carries an `ε > 0`, giving `n > k^{6+o(1)}`,
the same conclusion). The overlap bound `W ≤ k^k` is proved, not assumed. Because `BlockRadLB` is
a hypothesis (argument), not an `axiom`, `#print axioms not_powerful_of_large` shows ONLY
Mathlib's three axioms (`propext`, `Classical.choice`, `Quot.sound`), with `BlockRadLB`
discharged as a premise.

## What is left open

The unconditional Erdős #137 remains open, as does abc. The `g = 3` triple route gives `n > k^6`;
the analogous `g = 4` block route gives the threshold `n > k^4`, which together with Pandey's
unconditional squarefree-value count for `n < k^{5+δ}` would give full joint `(n, k)` finiteness.
Those last two inputs are not formalized here.
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## Basic facts about `F` and the triples tiling -/

/-- `F` splits as a product of an initial block and a shifted tail:
`F (a + b) n = F a n * F b (n + a)`. -/
lemma F_add (a b n : ℕ) : F (a + b) n = F a n * F b (n + a) := by
  unfold F
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring_nf

/-- `F a n` divides `F (a + b) n`. -/
lemma F_dvd_F_add (a b n : ℕ) : F a n ∣ F (a + b) n := by
  rw [F_add]; exact Dvd.intro _ rfl

/-- The product over the `⌊k/3⌋` triples, `∏_{j<⌊k/3⌋} F 3 (n + 3j)`, equals `F (3 * ⌊k/3⌋) n`. -/
lemma triples_prod_eq (k n : ℕ) :
    (∏ j ∈ Finset.range (k / 3), F 3 (n + 3 * j)) = F (3 * (k / 3)) n := by
  induction (k / 3) with
  | zero => simp [F]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have h3 : 3 * (t + 1) = 3 * t + 3 := by ring
    rw [h3, F_add]

/-- **Target part of #2 (combinatorial tiling):** the product of the triples divides `F k n`. -/
lemma triples_prod_dvd (k n : ℕ) :
    (∏ j ∈ Finset.range (k / 3), F 3 (n + 3 * j)) ∣ F k n := by
  rw [triples_prod_eq]
  have hk : k = 3 * (k / 3) + (k % 3) := by omega
  conv_rhs => rw [hk]
  exact F_dvd_F_add _ _ _

/-! ## The radical-of-product decomposition (fully proved)

We compare prime factorizations. For a prime `p`:
* `v_p (∏_j rad (F 3 (n+3j)))` counts the triples that `p` divides (each `rad` factor contributes
  exponent 0 or 1);
* `v_p (rad (F k n))` is `1` if `p ∣ F k n`, else `0`;
and a prime divides `F k n` iff it divides some triple (since the triples product divides `F k n`,
and conversely each triple divides `F k n`). The difference is the over-count exponent.
-/

/-- The block product `B k n = ∏_{j<⌊k/3⌋} F 3 (n+3j) = F (3⌊k/3⌋) n`: the part of `F k n`
covered by the triples (dropping the `k % 3` tail). -/
def B (k n : ℕ) : ℕ := ∏ j ∈ Finset.range (k / 3), F 3 (n + 3 * j)

/-- `overlap p = ∑_j [p ∈ (F 3 (n+3j)).primeFactors]` is the number of triples `p` divides.
This is exactly the multiplicity with which `p` is "counted in more than one triple". -/
def overlap (k n p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k / 3), if p ∈ (F 3 (n + 3 * j)).primeFactors then 1 else 0

/-- The over-count `W k n := ∏_{p ∈ (B k n).primeFactors} p ^ (overlap p − 1)`. This is the
correction for primes counted in more than one triple, taken over the prime support of
the triples **block** `B k n` (the natural home: a prime divides `B` iff it divides some triple). -/
def W (k n : ℕ) : ℕ :=
  ∏ p ∈ (B k n).primeFactors, p ^ (overlap k n p - 1)

/-- `B k n = F (3 * (k/3)) n`. -/
lemma B_eq (k n : ℕ) : B k n = F (3 * (k / 3)) n := triples_prod_eq k n

/-- `B k n` divides `F k n`. -/
lemma B_dvd_F (k n : ℕ) : B k n ∣ F k n := triples_prod_dvd k n

/-- `B k n ≠ 0` for `n ≥ 1`. -/
lemma B_ne_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : B k n ≠ 0 := by
  rw [B_eq]; exact F_ne_zero hn

/-- For `n ≥ 1` each triple `F 3 (n + 3j)` is nonzero. -/
lemma triple_ne_zero {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : F 3 (n + 3 * j) ≠ 0 :=
  F_ne_zero (by omega)

/-- `rad m ∣ m` for `m ≠ 0`. -/
lemma rad_dvd_self {m : ℕ} (_hm : m ≠ 0) : rad m ∣ m := by
  unfold rad; rw [Nat.support_factorization]; exact Nat.prod_primeFactors_dvd _

/-- The prime support of `rad m` is exactly `m.primeFactors` (for `m ≠ 0`). -/
lemma primeFactors_rad {m : ℕ} (hm : m ≠ 0) : (rad m).primeFactors = m.primeFactors := by
  apply Finset.Subset.antisymm
  · exact Nat.primeFactors_mono (rad_dvd_self hm) hm
  · intro p hp
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    -- p ∈ support of rad m since p ∈ m.primeFactors = support of the product
    have : p ∣ rad m := by
      unfold rad; rw [Nat.support_factorization]
      exact Finset.dvd_prod_of_mem _ hp
    exact Nat.mem_primeFactors.mpr ⟨hpprime, this, Nat.one_le_iff_ne_zero.mp (rad_pos m)⟩

/-- **General fact:** `rad m` is squarefree, so `(rad m).factorization p = 1` if `p ∈ m.primeFactors`,
else `0`. -/
lemma factorization_rad {m : ℕ} (hm : m ≠ 0) (p : ℕ) :
    (rad m).factorization p = if p ∈ m.primeFactors then 1 else 0 := by
  by_cases hp : p ∈ m.primeFactors
  · simp only [hp, if_true]
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    unfold rad
    rw [Nat.support_factorization]
    rw [Nat.factorization_prod_apply (by
      intro q hq; exact (Nat.prime_of_mem_primeFactors hq).ne_zero)]
    rw [Finset.sum_eq_single p]
    · exact Nat.Prime.factorization_self hpprime
    · intro q hq hqp
      rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hpprime (Nat.prime_of_mem_primeFactors hq)).mp hdvd).symm
    · intro h; exact absurd hp h
  · simp only [hp, if_false]
    by_cases hpp : p.Prime
    · rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      apply hp
      exact Nat.mem_primeFactors.mpr
        ⟨hpp, dvd_trans hdvd (rad_dvd_self hm), hm⟩
    · exact Nat.factorization_eq_zero_of_not_prime _ hpp

/-- The `p`-adic valuation of the product of triple-radicals equals `overlap k n p`. -/
lemma factorization_triples_rad (k n p : ℕ) (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))).factorization p = overlap k n p := by
  have hrad_ne : ∀ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j)) ≠ 0 := by
    intro j _; exact Nat.one_le_iff_ne_zero.mp (rad_pos _)
  rw [Nat.factorization_prod_apply hrad_ne]
  unfold overlap
  apply Finset.sum_congr rfl
  intro j _
  rw [factorization_rad (triple_ne_zero hn j)]

/-- The `p`-valuation of `rad (B k n)` is `1` if `p ∈ (B k n).primeFactors`, else `0`. -/
lemma factorization_rad_B {k n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (rad (B k n)).factorization p = if p ∈ (B k n).primeFactors then 1 else 0 :=
  factorization_rad (B_ne_zero hn k) p

/-- A prime in the support of `B k n` divides some triple, hence `overlap ≥ 1`. -/
lemma overlap_pos_of_mem_primeFactors {k n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (B k n).primeFactors) : 1 ≤ overlap k n p := by
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ B k n := Nat.dvd_of_mem_primeFactors hp
  -- p ∣ ∏ triples ⇒ p ∣ some triple
  have : ∃ j ∈ Finset.range (k / 3), p ∣ F 3 (n + 3 * j) := by
    rw [B] at hpdvd
    exact (Nat.Prime.prime hpprime).exists_mem_finset_dvd hpdvd
  obtain ⟨j, hj, hjdvd⟩ := this
  unfold overlap
  have hmem : p ∈ (F 3 (n + 3 * j)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hjdvd, triple_ne_zero hn j⟩
  have hle := Finset.single_le_sum
    (f := fun i => if p ∈ (F 3 (n + 3 * i)).primeFactors then (1:ℕ) else 0)
    (by intro i _; positivity) hj
  simpa [hmem] using hle

/-- If `overlap k n p ≥ 1` then `p ∈ (B k n).primeFactors` (it divides a triple, hence `B`). -/
lemma mem_primeFactors_of_overlap_pos {k n p : ℕ} (hn : 1 ≤ n) (h : 1 ≤ overlap k n p) :
    p ∈ (B k n).primeFactors := by
  unfold overlap at h
  -- some summand is 1, i.e. p ∈ primeFactors of some triple
  obtain ⟨j, hj, hjne⟩ : ∃ j ∈ Finset.range (k / 3), (if p ∈ (F 3 (n + 3 * j)).primeFactors then (1:ℕ) else 0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have : ∑ j ∈ Finset.range (k / 3), (if p ∈ (F 3 (n + 3 * j)).primeFactors then (1:ℕ) else 0) = 0 :=
      Finset.sum_eq_zero (fun j hj => hcon j hj)
    omega
  have hmem : p ∈ (F 3 (n + 3 * j)).primeFactors := by
    by_contra hc; simp [hc] at hjne
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
  have hpdvd_triple : p ∣ F 3 (n + 3 * j) := Nat.dvd_of_mem_primeFactors hmem
  have hpdvdB : p ∣ B k n := by
    rw [B]; exact dvd_trans hpdvd_triple (Finset.dvd_prod_of_mem _ hj)
  exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvdB, B_ne_zero hn k⟩

/-- For a prime power `q ^ e` with `q` prime, its `p`-valuation is `e` if `q = p`, else `0`. -/
private lemma factorization_prime_pow_apply {q : ℕ} (hq : q.Prime) (e p : ℕ) :
    (q ^ e).factorization p = if q = p then e else 0 := by
  rw [Nat.Prime.factorization_pow hq]
  rw [Finsupp.single_apply]

/-- The `p`-valuation of the over-count `W k n`. -/
lemma factorization_W {k n : ℕ} (_hn : 1 ≤ n) (p : ℕ) :
    (W k n).factorization p =
      if p ∈ (B k n).primeFactors then overlap k n p - 1 else 0 := by
  unfold W
  rw [Nat.factorization_prod_apply (by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  by_cases hp : p ∈ (B k n).primeFactors
  · simp only [hp, if_true]
    rw [Finset.sum_eq_single p]
    · have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      rw [factorization_prime_pow_apply hpprime]
      simp
    · intro q hq hqp
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
      rw [factorization_prime_pow_apply hqprime]
      simp [hqp]
    · intro h; exact absurd hp h
  · simp only [hp, if_false]
    apply Finset.sum_eq_zero
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [factorization_prime_pow_apply hqprime]
    have : q ≠ p := by rintro rfl; exact hp hq
    simp [this]


/-- **Radical-of-product decomposition, exact form.**
`∏_j rad (F 3 (n+3j)) = rad (B k n) * W k n`. Proved by comparing prime factorizations:
at each prime `p`, both sides have `p`-valuation `overlap k n p`. -/
theorem rad_triples_decomp {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))) = rad (B k n) * W k n := by
  have hR_ne : (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hradB_ne : rad (B k n) ≠ 0 := Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hW_ne : W k n ≠ 0 := by
    unfold W; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  apply Nat.eq_of_factorization_eq hR_ne (mul_ne_zero hradB_ne hW_ne)
  intro p
  rw [factorization_triples_rad k n p hn]
  rw [Nat.factorization_mul hradB_ne hW_ne]
  simp only [Finsupp.add_apply]
  rw [factorization_rad_B hn p, factorization_W hn p]
  by_cases hp : p ∈ (B k n).primeFactors
  · simp only [hp, if_true]
    have h1 : 1 ≤ overlap k n p := overlap_pos_of_mem_primeFactors hn hp
    omega
  · simp only [hp, if_false, add_zero]
    -- p ∉ primeFactors B ⇒ overlap = 0
    by_contra hcon
    have : 1 ≤ overlap k n p := by omega
    exact hp (mem_primeFactors_of_overlap_pos hn this)

/-- `rad` is monotone under divisibility: `a ∣ b`, `b ≠ 0` ⟹ `rad a ∣ rad b`
(their prime supports are nested). -/
lemma rad_dvd_rad_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : rad a ∣ rad b := by
  unfold rad
  rw [Nat.support_factorization, Nat.support_factorization]
  apply Finset.prod_dvd_prod_of_subset
  exact Nat.primeFactors_mono hab hb

/-- `rad (B k n) ∣ rad (F k n)`. -/
lemma rad_B_dvd_rad_F {k n : ℕ} (hn : 1 ≤ n) : rad (B k n) ∣ rad (F k n) :=
  rad_dvd_rad_of_dvd (F_ne_zero hn) (B_dvd_F k n)

/-- **Decomposition inequality (the usable form):**
`∏_j rad (F 3 (n+3j)) ≤ rad (F k n) * W k n`. -/
theorem rad_triples_le {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))) ≤ rad (F k n) * W k n := by
  rw [rad_triples_decomp hn]
  apply Nat.mul_le_mul_right
  exact Nat.le_of_dvd (rad_pos _) (rad_B_dvd_rad_F hn)

/-! ## Elementary size bounds on `F k n` (for converting a bound on `F` into pair-finiteness) -/

/-- `n ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the first factor is `n`, the rest are `≥ 1`). -/
lemma le_F {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : n ≤ F k n := by
  unfold F
  have hmem : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + 0) ∣ ∏ i ∈ Finset.range k, (n + i) := Finset.dvd_prod_of_mem _ hmem
  simpa using Nat.le_of_dvd (F_pos hn) hdvd

/-- `k ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the last factor `n+k-1 ≥ k` divides the product). -/
lemma le_F' {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : k ≤ F k n := by
  unfold F
  have hmem : (k - 1) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + (k - 1)) ∣ ∏ i ∈ Finset.range k, (n + i) := Finset.dvd_prod_of_mem _ hmem
  have : k ≤ n + (k - 1) := by omega
  exact le_trans this (Nat.le_of_dvd (F_pos hn) hdvd)


/-! ## Counting multiples of a prime in an interval (for the overlap bound) -/

/-- **Exact count** of multiples of `p` in `(a, b]`: `#{x ∈ Ioc a b | p ∣ x} = b/p − a/p`. -/
theorem Ioc_dvd_count (a b p : ℕ) (hab : a ≤ b) :
    #{x ∈ Finset.Ioc a b | p ∣ x} = b / p - a / p := by
  have h1 : #{x ∈ Finset.Ioc 0 b | p ∣ x} = b / p := Nat.Ioc_filter_dvd_card_eq_div b p
  have h2 : #{x ∈ Finset.Ioc 0 a | p ∣ x} = a / p := Nat.Ioc_filter_dvd_card_eq_div a p
  have hsplit : #{x ∈ Finset.Ioc 0 b | p ∣ x}
      = #{x ∈ Finset.Ioc 0 a | p ∣ x} + #{x ∈ Finset.Ioc a b | p ∣ x} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
    · apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]; simp
  omega

/-- The number of multiples of `p` in an interval of length `L` is at most `⌊L/p⌋ + 1`. -/
theorem Ioc_dvd_le (a L p : ℕ) (hp : 1 ≤ p) :
    #{x ∈ Finset.Ioc a (a + L) | p ∣ x} ≤ L / p + 1 := by
  rw [Ioc_dvd_count a (a + L) p (Nat.le_add_right a L)]
  have hpp : 0 < p := hp
  have h6 : (a + L) / p = (a / p + L / p) + (a % p + L % p) / p := by
    have h5 : (a + L) = p * (a / p + L / p) + (a % p + L % p) := by
      have hma : p * (a / p + L / p) = p * (a / p) + p * (L / p) := by ring
      have h1 : p * (a / p) + a % p = a := Nat.div_add_mod a p
      have h2 : p * (L / p) + L % p = L := Nat.div_add_mod L p
      rw [hma]; omega
    rw [h5, Nat.mul_add_div hpp]
  have h7 : (a % p + L % p) / p ≤ 1 := by
    have h3 : a % p < p := Nat.mod_lt _ hpp
    have h4 : L % p < p := Nat.mod_lt _ hpp
    rw [Nat.div_le_iff_le_mul_add_pred hpp]; omega
  rw [Nat.sub_le_iff_le_add, h6]; omega

/-! ## The overlap bound `W k n ≤ k^k` (proved) -/

/-- **Overlap bound (combinatorial core).** `overlap k n p ≤ ⌊k/p⌋ + 1` for `n ≥ 1`.
The `⌊k/3⌋` triples span `≤ k` consecutive integers, and a prime `p` divides at most `⌊k/p⌋ + 1`
of any `≤ k` consecutive integers (hence at most that many triples). -/
lemma overlap_le {k n p : ℕ} (hn : 1 ≤ n) : overlap k n p ≤ k / p + 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0; unfold overlap
    -- p = 0 divides no triple, so overlap = 0
    have hz : (∑ j ∈ Finset.range (k / 3),
        (if (0 : ℕ) ∈ (F 3 (n + 3 * j)).primeFactors then (1 : ℕ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hnotmem : (0 : ℕ) ∉ (F 3 (n + 3 * j)).primeFactors := by
        intro h; exact absurd (Nat.prime_of_mem_primeFactors h) Nat.not_prime_zero
      rw [if_neg hnotmem]
    rw [hz]; omega
  · -- map each counted triple j to a divisible integer in (n−1, n−1+3⌊k/3⌋]
    set t := k / 3 with ht
    set m := 3 * t with hm
    have hmk : m ≤ k := by rw [hm, ht]; omega
    have hkey : overlap k n p ≤ #{x ∈ Finset.Ioc (n - 1) (n - 1 + m) | p ∣ x} := by
      unfold overlap
      have hsum : (∑ j ∈ Finset.range t,
          (if p ∈ (F 3 (n + 3 * j)).primeFactors then (1 : ℕ) else 0))
          = #{j ∈ Finset.range t | p ∈ (F 3 (n + 3 * j)).primeFactors} := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          mul_one]
      rw [show k / 3 = t from rfl, hsum]
      apply Finset.card_le_card_of_injOn
        (fun j => if p ∣ (n + 3 * j) then n + 3 * j
                  else if p ∣ (n + 3 * j + 1) then n + 3 * j + 1 else n + 3 * j + 2)
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨hjt, hmem⟩ := hj
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
        have hpdvd : p ∣ F 3 (n + 3 * j) := Nat.dvd_of_mem_primeFactors hmem
        have hdvd3 : p ∣ (n + 3 * j) ∨ p ∣ (n + 3 * j + 1) ∨ p ∣ (n + 3 * j + 2) := by
          have hF : F 3 (n + 3 * j) = (n + 3 * j) * ((n + 3 * j + 1) * (n + 3 * j + 2)) := by
            unfold F
            rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
            ring
          rw [hF] at hpdvd
          rcases (Nat.Prime.dvd_mul hpp).mp hpdvd with h | h
          · exact Or.inl h
          · rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
            · exact Or.inr (Or.inl h')
            · exact Or.inr (Or.inr h')
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · split_ifs <;> omega
        · have hjm : 3 * j + 2 < m := by rw [hm]; omega
          split_ifs <;> omega
        · split_ifs with h1 h2
          · exact h1
          · exact h2
          · rcases hdvd3 with h | h | h
            · exact absurd h h1
            · exact absurd h h2
            · exact h
      · intro j hj j' hj' heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj hj'
        have hbound : ∀ i, (if p ∣ (n + 3 * i) then n + 3 * i
            else if p ∣ (n + 3 * i + 1) then n + 3 * i + 1 else n + 3 * i + 2)
            ∈ Finset.Icc (n + 3 * i) (n + 3 * i + 2) := by
          intro i; simp only [Finset.mem_Icc]; split_ifs <;> omega
        have h1 := hbound j; have h2 := hbound j'
        simp only [Finset.mem_Icc] at h1 h2
        simp only at heq
        rw [heq] at h1
        omega
    refine le_trans hkey ?_
    refine le_trans (Ioc_dvd_le (n - 1) m p hp) ?_
    have : m / p ≤ k / p := Nat.div_le_div_right hmk
    omega

/-- For a prime `p`, `⌊k/p⌋ ≤ (k!).factorization p` (the `i = 1` term of Legendre's formula). -/
lemma div_le_factorization_factorial {k p : ℕ} (hp : p.Prime) :
    k / p ≤ (Nat.factorial k).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p k))]
  by_cases hpk : 1 ≤ Nat.log p k
  · have hmem : 1 ∈ Finset.Ico 1 (Nat.log p k + 1) := by
      simp only [Finset.mem_Ico]; omega
    calc k / p = k / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), k / p ^ i :=
          Finset.single_le_sum (f := fun i => k / p ^ i) (by intro i _; positivity) hmem
  · have hlt : k < p := by
      by_contra hc; push_neg at hc
      exact absurd (Nat.log_pos hp.one_lt hc) (by omega)
    rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _

/-- **Overlap product divides `k!`.** `W k n ∣ k!`: per prime `p`,
`v_p(W) = overlap − 1 ≤ ⌊k/p⌋ ≤ v_p(k!)` (Legendre). -/
theorem W_dvd_factorial {k n : ℕ} (hn : 1 ≤ n) : W k n ∣ Nat.factorial k := by
  have hWne : W k n ≠ 0 := by
    unfold W; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd hWne (Nat.factorial_ne_zero k)]
  intro p
  rw [factorization_W hn p]
  by_cases hp : p ∈ (B k n).primeFactors
  · simp only [hp, if_true]
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have h1 : overlap k n p ≤ k / p + 1 := overlap_le hn
    have h2 : k / p ≤ (Nat.factorial k).factorization p := div_le_factorization_factorial hpp
    omega
  · simp only [hp, if_false]; exact Nat.zero_le _

/-- **Overlap bound: `W k n ≤ k^k`.** Since `W ∣ k!` (Legendre) and `k! ≤ k^k`; on the log scale
`log W ≤ k log k + O(k)`. -/
theorem W_le_pow {k n : ℕ} (hn : 1 ≤ n) : W k n ≤ k ^ k := by
  calc W k n ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) (W_dvd_factorial hn)
    _ ≤ k ^ k := Nat.factorial_le_pow k

/-- **Elementary lower bound `n^k ≤ F k n`.** Each of the `k` factors of `F k n` is `≥ n`. This is
the size input (`log F ≥ k log n`) that turns `W ≤ k^k` into the clean `n > k^6` threshold. -/
theorem pow_le_F {k n : ℕ} : n ^ k ≤ F k n := by
  unfold F
  calc n ^ k = ∏ _i ∈ Finset.range k, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (n + i) :=
        Finset.prod_le_prod' (fun i _ => Nat.le_add_right n i)

/-! ## The genuine abc input and the headline theorem -/

/-- **(H) Block radical lower bound (abc-extremal form).** Langevin/abc applied to each squarefree
cubic triple `g(m) = m(m+1)(m+2)` (`rad (F 3 m) ≫_ε m^{2−ε}`), assembled over the `⌊k/3⌋` triples:
`(F k n)^{2/3} ≤ ∏ rad over triples`, uniformly in `(k, n)`. This is the genuine abc-conditional
input (abc itself is NOT formalized). Stated in the `ε = 0`, `C = 1` extremal form, which yields
the clean threshold `n > k^6`; the realistic `ε > 0` Langevin bound gives `n > k^{6 + o(1)}`. -/
def BlockRadLB : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ ((2 : ℝ) / 3) ≤
      ((∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j)) : ℕ) : ℝ)

/-- **Headline.** Under the block radical lower bound `BlockRadLB` (the genuine abc input, the
ONLY hypothesis), for `k ≥ 3` and `n > k^6` the product `F k n` is **not powerful**. The overlap
`W ≤ k^k` is proved (`W_le_pow`), not assumed. -/
theorem not_powerful_of_large (hBlock : BlockRadLB) {k n : ℕ}
    (hk : 3 ≤ k) (hn : k ^ 6 < n) : ¬ Powerful (F k n) := by
  intro hPow
  have hn1 : 1 ≤ n := by have : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega); omega
  have hkpos : 0 < k := by omega
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn1
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  have hblk := hBlock k n hk hn1
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * (W k n : ℝ) := by
    rw [hPrd]; exact_mod_cast rad_triples_le hn1
  have hradsq : (rad (F k n) : ℝ) ^ 2 ≤ Φ := by
    rw [hΦ]; exact_mod_cast powerful_rad_sq_le hFne hPow
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hW : (W k n : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast W_le_pow hn1
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  -- Chain: Φ^{2/3} ≤ ∏rad ≤ rad·W ≤ rad·k^k; square it.
  have hchain2 : Φ ^ ((2 : ℝ) / 3) ≤ (rad (F k n) : ℝ) * (k : ℝ) ^ k :=
    le_trans (le_trans hblk hdecomp) (mul_le_mul_of_nonneg_left hW hradpos)
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ ((2 : ℝ) / 3)) ^ 2 ≤ ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain2 2
  have hL : (Φ ^ ((2 : ℝ) / 3)) ^ 2 = Φ ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (Φ ^ ((2:ℝ)/3)) 2, ← Real.rpow_mul (le_of_lt hΦpos)]
    norm_num
  have hR : ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2
      = (rad (F k n) : ℝ) ^ 2 * ((k : ℝ) ^ k) ^ 2 := by ring
  rw [hL, hR] at hsq
  have hk2k : ((k : ℝ) ^ k) ^ 2 = (k : ℝ) ^ (2 * k) := by rw [← pow_mul]; ring_nf
  rw [hk2k] at hsq
  have hk2kpos : (0 : ℝ) < (k : ℝ) ^ (2 * k) := by positivity
  have hsq2 : Φ ^ ((4 : ℝ) / 3) ≤ Φ * (k : ℝ) ^ (2 * k) :=
    le_trans hsq (mul_le_mul_of_nonneg_right hradsq (le_of_lt hk2kpos))
  have hΦsplit : Φ ^ ((4 : ℝ) / 3) = Φ ^ ((1 : ℝ) / 3) * Φ := by
    rw [show (4 : ℝ)/3 = (1:ℝ)/3 + 1 by norm_num, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hsq2
  have hcube : Φ ^ ((1 : ℝ) / 3) ≤ (k : ℝ) ^ (2 * k) := by
    have hsq3 : Φ ^ ((1 : ℝ) / 3) * Φ ≤ (k : ℝ) ^ (2 * k) * Φ := by
      rw [mul_comm ((k : ℝ) ^ (2 * k)) Φ]; exact hsq2
    exact le_of_mul_le_mul_right hsq3 hΦpos
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hncube : ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) ≤ Φ ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hnk_nonneg hFlow (by norm_num)
  have hkey : ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) ≤ (k : ℝ) ^ (2 * k) := le_trans hncube hcube
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hkRpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  -- rewrite both sides as `· ^ ((k:ℝ)/3)` of the bases `n` and `k^6`
  have hLrw : ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) = (n : ℝ) ^ ((k : ℝ) / 3) := by
    rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt hnpos)]
    congr 1; ring
  have hRrw : (k : ℝ) ^ (2 * k) = ((k : ℝ) ^ 6) ^ ((k : ℝ) / 3) := by
    have e1 : (k : ℝ) ^ (2 * k) = (k : ℝ) ^ ((2 * k : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    have e2 : ((k : ℝ) ^ 6 : ℝ) = (k : ℝ) ^ ((6 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    rw [e1, e2, ← Real.rpow_mul (le_of_lt hkRpos)]
    congr 1; push_cast; ring
  rw [hLrw, hRrw] at hkey
  have hexp_pos : (0 : ℝ) < (k : ℝ) / 3 := by positivity
  have hnle : (n : ℝ) ≤ (k : ℝ) ^ 6 := by
    by_contra hcon
    push_neg at hcon
    have hk6pos : (0 : ℝ) ≤ (k : ℝ) ^ 6 := by positivity
    have := Real.rpow_lt_rpow hk6pos hcon hexp_pos
    linarith [hkey, this]
  have hn6 : ((k : ℝ) ^ 6) < (n : ℝ) := by
    calc (k : ℝ) ^ 6 = ((k ^ 6 : ℕ) : ℝ) := by push_cast; ring
      _ < (n : ℝ) := by exact_mod_cast hn
  linarith [hnle, hn6]

/-- **Per-fixed-`k` finiteness.** For each `k ≥ 3`, under `BlockRadLB`, the set of `n ≥ 1` with
`F k n` powerful is finite (all satisfy `n ≤ k^6`); the triple-route analogue of `erdos137_finite`. -/
theorem not_powerful_finite (hBlock : BlockRadLB) {k : ℕ} (hk : 3 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (k ^ 6))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  by_contra hcon
  push_neg at hcon
  exact not_powerful_of_large hBlock hk hcon hn.2

end  -- noncomputable section

end Erdos137