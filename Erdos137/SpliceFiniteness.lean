import Erdos137.Finiteness
import Erdos137.JointFiniteness
import Erdos137.SmoothRefinement
import Erdos137.TaoPoint

namespace Erdos137

/-!
# Erdős Problem #137: the honest `g = 5` per-`k` bound and the abstract splice machine

`Erdos137/JointFiniteness.lean` formalizes the radical-decomposition argument for triples (`g = 3`);
`Erdos137/SmoothRefinement.lean` adds the smooth-part saving. This file develops the corresponding
quintic (`g = 5`) block machinery and separates two logically distinct outputs.

## What is formalized

* **`g5_finiteness` / `powerful_bound_g5` — per-`k` finiteness from one block input.** From the single
  tail-absorbed hypothesis `BlockRadLB5`, for every fixed `k ≥ 5` the set of `n ≥ 1` with `F k n`
  powerful is finite; precisely, every such `n` satisfies `n ≤ Msplice k = (k^{2k})^5 · P k^{10}`. The
  proof is the formalized master inequality `n^{3k} · L k^5 ≤ (k^{2k})^5 · P k^{10}` (`master_ineq5`),
  using the quintic block radical input, the overlap bound `W5 ≤ k^k`, and the smooth-part refinement.
  The guard `5 ≤ k` is essential: for `k < 5` there are no quintic blocks (`⌊k/5⌋ = 0`). This is a
  per-`k` finiteness statement, NOT joint finiteness in `(n, k)`.

* **`abstract_splice_no_counterexamples` — an honest range-splice template.** Parametric in two
  predicates `Mid High : ℕ → ℕ → Prop`. Given (i) `CoversAll Mid High` — every `(k, n)` with `k ≥ 3`,
  `1 ≤ n` lies in `n ≤ k`, `Mid k n`, or `High k n`; (ii) `PrimeInBlockOnRange Mid` — a prime `p > k`
  that is a term of the block on the middle range; (iii) a high-range proof
  `High k n → ¬ Powerful (F k n)`; it proves `¬ Powerful (F k n)` for all such `(k, n)`. The small
  range `n ≤ k` is discharged unconditionally by Bertrand via `upper_half_prime_not_powerful`.

The intended Pandey-free no-gap splice is an ASYMPTOTIC pen-and-paper reading of
`abstract_splice_no_counterexamples`: take `Mid` = the Baker–Harman–Pintz range
`k < n ≤ k^{40/21−o(1)}` (where BHP supplies a prime `p > k` in `[n, n+k-1]`) and `High` = the
Mertens-sharpened quintic range `n > k^{5/3+o(1)}`. Since `5/3 < 40/21`, these ranges overlap for all
sufficiently large `k`, after the usual finite exceptional range (and `k = 3, 4`, handled by the triple
route) is absorbed. Lean does NOT formalize Baker–Harman–Pintz, Mertens, or this asymptotic coverage;
they enter only as the external premises of the abstract splice theorem, and a faithful instantiation
would carry a finite-exception clause.

## What is proved vs. hypothesized

* **Proved (Mathlib's three axioms only):** the `g = 5` block product identities, the radical product
  decomposition, `W5_le_pow` (`W5 ∣ k!`, Legendre), `master_ineq5`, `not_powerful_g5`,
  `powerful_bound_g5`, `g5_finiteness`, the unconditional small-`n` lemma
  `upper_half_prime_not_powerful` (Bertrand), `prime_range_not_powerful`, and
  `abstract_splice_no_counterexamples`.
* **Hypotheses (analytic inputs, NOT formalized):** `BlockRadLB5` packages the abc/Langevin quintic
  block estimate, its constants, the epsilon loss, and the omitted tail into one explicit normalized
  hypothesis. `PrimeInBlockOnRange`, `CoversAll`, and the high-range proof are premises of the abstract
  splice (encoding BHP + Mertens + the exact exponents on the intended instantiation). All enter as
  premises, so they do NOT appear in the axiom footprint of any theorem. Unconditional Erdős #137 and
  abc remain open.
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## PART A — the `g = 5` block machinery (parallel to the triple tiling) -/

/-- The product over the `⌊k/5⌋` quintic blocks, `∏_{j<⌊k/5⌋} F 5 (n + 5j)`, equals
`F (5 * ⌊k/5⌋) n`. -/
lemma blocks5_prod_eq (k n : ℕ) :
    (∏ j ∈ Finset.range (k / 5), F 5 (n + 5 * j)) = F (5 * (k / 5)) n := by
  induction (k / 5) with
  | zero => simp [F]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have h5 : 5 * (t + 1) = 5 * t + 5 := by ring
    rw [h5, F_add]

/-- The product of the quintic blocks divides `F k n`. -/
lemma blocks5_prod_dvd (k n : ℕ) :
    (∏ j ∈ Finset.range (k / 5), F 5 (n + 5 * j)) ∣ F k n := by
  rw [blocks5_prod_eq]
  have hk : k = 5 * (k / 5) + (k % 5) := by omega
  conv_rhs => rw [hk]
  exact F_dvd_F_add _ _ _

/-- The block product `B5 k n = ∏_{j<⌊k/5⌋} F 5 (n+5j) = F (5⌊k/5⌋) n`: the part of `F k n`
covered by the quintic blocks (dropping the `k % 5` tail). -/
def B5 (k n : ℕ) : ℕ := ∏ j ∈ Finset.range (k / 5), F 5 (n + 5 * j)

/-- `overlap5 p = ∑_j [p ∈ (F 5 (n+5j)).primeFactors]` is the number of quintic blocks `p` divides. -/
def overlap5 (k n p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k / 5), if p ∈ (F 5 (n + 5 * j)).primeFactors then 1 else 0

/-- The over-count `W5 k n := ∏_{p ∈ (B5 k n).primeFactors} p ^ (overlap5 p − 1)`. -/
def W5 (k n : ℕ) : ℕ :=
  ∏ p ∈ (B5 k n).primeFactors, p ^ (overlap5 k n p - 1)

/-- `B5 k n = F (5 * (k/5)) n`. -/
lemma B5_eq (k n : ℕ) : B5 k n = F (5 * (k / 5)) n := blocks5_prod_eq k n

/-- **`B5 k n` divides `F k n`** (analogue of `triples_prod_dvd`). -/
lemma B5_dvd_F (k n : ℕ) : B5 k n ∣ F k n := blocks5_prod_dvd k n

/-- `B5 k n ≠ 0` for `n ≥ 1`. -/
lemma B5_ne_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : B5 k n ≠ 0 := by
  rw [B5_eq]; exact F_ne_zero hn

/-- For `n ≥ 1` each quintic block `F 5 (n + 5j)` is nonzero. -/
lemma block5_ne_zero {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : F 5 (n + 5 * j) ≠ 0 :=
  F_ne_zero (by omega)

/-- The `p`-adic valuation of the product of the block radicals equals `overlap5 k n p`. -/
lemma factorization_blocks5_rad (k n p : ℕ) (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))).factorization p = overlap5 k n p := by
  have hrad_ne : ∀ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j)) ≠ 0 := by
    intro j _; exact Nat.one_le_iff_ne_zero.mp (rad_pos _)
  rw [Nat.factorization_prod_apply hrad_ne]
  unfold overlap5
  apply Finset.sum_congr rfl
  intro j _
  rw [factorization_rad (block5_ne_zero hn j)]

/-- The `p`-valuation of `rad (B5 k n)` is `1` if `p ∈ (B5 k n).primeFactors`, else `0`. -/
lemma factorization_rad_B5 {k n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (rad (B5 k n)).factorization p = if p ∈ (B5 k n).primeFactors then 1 else 0 :=
  factorization_rad (B5_ne_zero hn k) p

/-- A prime in the support of `B5 k n` divides some block, hence `overlap5 ≥ 1`. -/
lemma overlap5_pos_of_mem_primeFactors {k n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (B5 k n).primeFactors) : 1 ≤ overlap5 k n p := by
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ B5 k n := Nat.dvd_of_mem_primeFactors hp
  have : ∃ j ∈ Finset.range (k / 5), p ∣ F 5 (n + 5 * j) := by
    rw [B5] at hpdvd
    exact (Nat.Prime.prime hpprime).exists_mem_finset_dvd hpdvd
  obtain ⟨j, hj, hjdvd⟩ := this
  unfold overlap5
  have hmem : p ∈ (F 5 (n + 5 * j)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hjdvd, block5_ne_zero hn j⟩
  have hle := Finset.single_le_sum
    (f := fun i => if p ∈ (F 5 (n + 5 * i)).primeFactors then (1:ℕ) else 0)
    (by intro i _; positivity) hj
  simpa [hmem] using hle

/-- If `overlap5 k n p ≥ 1` then `p ∈ (B5 k n).primeFactors`. -/
lemma mem_primeFactors_of_overlap5_pos {k n p : ℕ} (hn : 1 ≤ n) (h : 1 ≤ overlap5 k n p) :
    p ∈ (B5 k n).primeFactors := by
  unfold overlap5 at h
  obtain ⟨j, hj, hjne⟩ : ∃ j ∈ Finset.range (k / 5),
      (if p ∈ (F 5 (n + 5 * j)).primeFactors then (1:ℕ) else 0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have : ∑ j ∈ Finset.range (k / 5),
        (if p ∈ (F 5 (n + 5 * j)).primeFactors then (1:ℕ) else 0) = 0 :=
      Finset.sum_eq_zero (fun j hj => hcon j hj)
    omega
  have hmem : p ∈ (F 5 (n + 5 * j)).primeFactors := by
    by_contra hc; simp [hc] at hjne
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
  have hpdvd_block : p ∣ F 5 (n + 5 * j) := Nat.dvd_of_mem_primeFactors hmem
  have hpdvdB : p ∣ B5 k n := by
    rw [B5]; exact dvd_trans hpdvd_block (Finset.dvd_prod_of_mem _ hj)
  exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvdB, B5_ne_zero hn k⟩

/-- For a prime power `q ^ e` with `q` prime, its `p`-valuation is `e` if `q = p`, else `0`. -/
private lemma factorization_prime_pow_apply5 {q : ℕ} (hq : q.Prime) (e p : ℕ) :
    (q ^ e).factorization p = if q = p then e else 0 := by
  rw [Nat.Prime.factorization_pow hq]
  rw [Finsupp.single_apply]

/-- The `p`-valuation of the over-count `W5 k n`. -/
lemma factorization_W5 {k n : ℕ} (_hn : 1 ≤ n) (p : ℕ) :
    (W5 k n).factorization p =
      if p ∈ (B5 k n).primeFactors then overlap5 k n p - 1 else 0 := by
  unfold W5
  rw [Nat.factorization_prod_apply (by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  by_cases hp : p ∈ (B5 k n).primeFactors
  · simp only [hp, if_true]
    rw [Finset.sum_eq_single p]
    · have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      rw [factorization_prime_pow_apply5 hpprime]
      simp
    · intro q hq hqp
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
      rw [factorization_prime_pow_apply5 hqprime]
      simp [hqp]
    · intro h; exact absurd hp h
  · simp only [hp, if_false]
    apply Finset.sum_eq_zero
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [factorization_prime_pow_apply5 hqprime]
    have : q ≠ p := by rintro rfl; exact hp hq
    simp [this]

/-- **Radical-of-product decomposition (g = 5), exact form.**
`∏_j rad (F 5 (n+5j)) = rad (B5 k n) * W5 k n`. -/
theorem rad_blocks5_decomp {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))) = rad (B5 k n) * W5 k n := by
  have hR_ne : (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hradB_ne : rad (B5 k n) ≠ 0 := Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hW_ne : W5 k n ≠ 0 := by
    unfold W5; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  apply Nat.eq_of_factorization_eq hR_ne (mul_ne_zero hradB_ne hW_ne)
  intro p
  rw [factorization_blocks5_rad k n p hn]
  rw [Nat.factorization_mul hradB_ne hW_ne]
  simp only [Finsupp.add_apply]
  rw [factorization_rad_B5 hn p, factorization_W5 hn p]
  by_cases hp : p ∈ (B5 k n).primeFactors
  · simp only [hp, if_true]
    have h1 : 1 ≤ overlap5 k n p := overlap5_pos_of_mem_primeFactors hn hp
    omega
  · simp only [hp, if_false, add_zero]
    by_contra hcon
    have : 1 ≤ overlap5 k n p := by omega
    exact hp (mem_primeFactors_of_overlap5_pos hn this)

/-- `rad (B5 k n) ∣ rad (F k n)`. -/
lemma rad_B5_dvd_rad_F {k n : ℕ} (hn : 1 ≤ n) : rad (B5 k n) ∣ rad (F k n) :=
  rad_dvd_rad_of_dvd (F_ne_zero hn) (B5_dvd_F k n)

/-- **Decomposition inequality (the usable form, g = 5):**
`∏_j rad (F 5 (n+5j)) ≤ rad (F k n) * W5 k n` (analogue of `rad_triples_le`). -/
theorem rad_5blocks_le {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))) ≤ rad (F k n) * W5 k n := by
  rw [rad_blocks5_decomp hn]
  apply Nat.mul_le_mul_right
  exact Nat.le_of_dvd (rad_pos _) (rad_B5_dvd_rad_F hn)

/-! ### The overlap bound `W5 k n ≤ k^k` -/

/-- **Overlap bound (combinatorial core, g = 5).** `overlap5 k n p ≤ ⌊k/p⌋ + 1` for `n ≥ 1`.
The `⌊k/5⌋` blocks span `≤ k` consecutive integers, and a prime `p` divides at most `⌊k/p⌋ + 1`
of any `≤ k` consecutive integers. -/
lemma overlap5_le {k n p : ℕ} (hn : 1 ≤ n) : overlap5 k n p ≤ k / p + 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0; unfold overlap5
    have hz : (∑ j ∈ Finset.range (k / 5),
        (if (0 : ℕ) ∈ (F 5 (n + 5 * j)).primeFactors then (1 : ℕ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hnotmem : (0 : ℕ) ∉ (F 5 (n + 5 * j)).primeFactors := by
        intro h; exact absurd (Nat.prime_of_mem_primeFactors h) Nat.not_prime_zero
      rw [if_neg hnotmem]
    rw [hz]; omega
  · set t := k / 5 with ht
    set m := 5 * t with hm
    have hmk : m ≤ k := by rw [hm, ht]; omega
    have hkey : overlap5 k n p ≤ #{x ∈ Finset.Ioc (n - 1) (n - 1 + m) | p ∣ x} := by
      unfold overlap5
      have hsum : (∑ j ∈ Finset.range t,
          (if p ∈ (F 5 (n + 5 * j)).primeFactors then (1 : ℕ) else 0))
          = #{j ∈ Finset.range t | p ∈ (F 5 (n + 5 * j)).primeFactors} := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          mul_one]
      rw [show k / 5 = t from rfl, hsum]
      apply Finset.card_le_card_of_injOn
        (fun j => if p ∣ (n + 5 * j) then n + 5 * j
                  else if p ∣ (n + 5 * j + 1) then n + 5 * j + 1
                  else if p ∣ (n + 5 * j + 2) then n + 5 * j + 2
                  else if p ∣ (n + 5 * j + 3) then n + 5 * j + 3
                  else n + 5 * j + 4)
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨hjt, hmem⟩ := hj
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
        have hpdvd : p ∣ F 5 (n + 5 * j) := Nat.dvd_of_mem_primeFactors hmem
        have hdvd5 : p ∣ (n + 5 * j) ∨ p ∣ (n + 5 * j + 1) ∨ p ∣ (n + 5 * j + 2)
            ∨ p ∣ (n + 5 * j + 3) ∨ p ∣ (n + 5 * j + 4) := by
          have hF : F 5 (n + 5 * j) = (n + 5 * j) * ((n + 5 * j + 1)
              * ((n + 5 * j + 2) * ((n + 5 * j + 3) * (n + 5 * j + 4)))) := by
            unfold F
            rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
              Finset.prod_range_succ, Finset.prod_range_one]
            ring
          rw [hF] at hpdvd
          rcases (Nat.Prime.dvd_mul hpp).mp hpdvd with h | h
          · exact Or.inl h
          rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
          · exact Or.inr (Or.inl h')
          rcases (Nat.Prime.dvd_mul hpp).mp h' with h'' | h''
          · exact Or.inr (Or.inr (Or.inl h''))
          rcases (Nat.Prime.dvd_mul hpp).mp h'' with h''' | h'''
          · exact Or.inr (Or.inr (Or.inr (Or.inl h''')))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h''')))
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · split_ifs <;> omega
        · have hjm : 5 * j + 4 < m := by rw [hm]; omega
          split_ifs <;> omega
        · split_ifs with h1 h2 h3 h4
          · exact h1
          · exact h2
          · exact h3
          · exact h4
          · rcases hdvd5 with h | h | h | h | h
            · exact absurd h h1
            · exact absurd h h2
            · exact absurd h h3
            · exact absurd h h4
            · exact h
      · intro j hj j' hj' heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj hj'
        have hbound : ∀ i, (if p ∣ (n + 5 * i) then n + 5 * i
            else if p ∣ (n + 5 * i + 1) then n + 5 * i + 1
            else if p ∣ (n + 5 * i + 2) then n + 5 * i + 2
            else if p ∣ (n + 5 * i + 3) then n + 5 * i + 3
            else n + 5 * i + 4)
            ∈ Finset.Icc (n + 5 * i) (n + 5 * i + 4) := by
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

/-- **Overlap product divides `k!` (g = 5).** `W5 k n ∣ k!`. -/
theorem W5_dvd_factorial {k n : ℕ} (hn : 1 ≤ n) : W5 k n ∣ Nat.factorial k := by
  have hWne : W5 k n ≠ 0 := by
    unfold W5; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd hWne (Nat.factorial_ne_zero k)]
  intro p
  rw [factorization_W5 hn p]
  by_cases hp : p ∈ (B5 k n).primeFactors
  · simp only [hp, if_true]
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have h1 : overlap5 k n p ≤ k / p + 1 := overlap5_le hn
    have h2 : k / p ≤ (Nat.factorial k).factorization p := div_le_factorization_factorial hpp
    omega
  · simp only [hp, if_false]; exact Nat.zero_le _

/-- **Overlap bound (g = 5): `W5 k n ≤ k^k`.** Since `W5 ∣ k!` (Legendre) and `k! ≤ k^k`. -/
theorem W5_le_pow {k n : ℕ} (hn : 1 ≤ n) : W5 k n ≤ k ^ k := by
  calc W5 k n ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) (W5_dvd_factorial hn)
    _ ≤ k ^ k := Nat.factorial_le_pow k

/-! ### The genuine abc input (g = 5) and the master inequality -/

/-- Tail-absorbed quintic block radical input. This is a NORMALIZED asymptotic
hypothesis, NOT the literal blockwise abc/Langevin statement: it packages the
abc/Langevin constant, the epsilon loss, and the omitted `k mod 5` tail into one
explicit hypothesis. The guard `5 ≤ k` is ESSENTIAL: for `k < 5` there are no
quintic blocks (`⌊k/5⌋ = 0`), the RHS is the empty product `1`, and the bound
`(F k n)^{4/5} ≤ 1` would be false — i.e. the hypothesis would be inconsistent. -/
def BlockRadLB5 : Prop :=
  ∀ k n : ℕ, 5 ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ ((4 : ℝ) / 5) ≤
      ((∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j)) : ℕ) : ℝ)

/-- **Smooth-refined master inequality (g = 5).** Under `BlockRadLB5`, for `k ≥ 5` and a powerful
`F k n` with `n ≥ 1`:  `n^{3k} · L k ^ 5 ≤ (k^{2k})^5 · P k ^ 10`.

Derivation (mirroring `master_ineq`): `Φ^{4/5} ≤ ∏rad ≤ rad·W5 ≤ rad·k^k`; squaring gives
`Φ^{8/5} ≤ rad^2 · k^{2k}`; feeding `smooth_refinement` (`rad^2 · L ≤ Φ · P^2`) and dividing by `Φ`
(using `8/5 = 3/5 + 1`) gives `Φ^{3/5} · L ≤ P^2 · k^{2k}`; with `Φ ≥ n^k` and raising to the 5th
power, `n^{3k} · L^5 ≤ (P^2 · k^{2k})^5 = (k^{2k})^5 · P^{10}`. -/
theorem master_ineq5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ (3 * k) * (L k : ℝ) ^ 5 ≤ ((k : ℝ) ^ (2 * k)) ^ 5 * (P k : ℝ) ^ 10 := by
  have hkpos : 0 < k := by omega
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  have hLpos : (0 : ℝ) < (L k : ℝ) := by exact_mod_cast L_pos k
  -- Block chain: Φ^{4/5} ≤ ∏rad ≤ rad·W5 ≤ rad·k^k.
  have hblk := hBlock5 k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * (W5 k n : ℝ) := by
    rw [hPrd]; exact_mod_cast rad_5blocks_le hn
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hW : (W5 k n : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast W5_le_pow hn
  have hchain : Φ ^ ((4 : ℝ) / 5) ≤ (rad (F k n) : ℝ) * (k : ℝ) ^ k :=
    le_trans (le_trans hblk hdecomp) (mul_le_mul_of_nonneg_left hW hradpos)
  -- Square: Φ^{8/5} ≤ rad^2 · k^{2k}.
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ ((4 : ℝ) / 5) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ ((4 : ℝ) / 5)) ^ 2 ≤ ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hL85 : (Φ ^ ((4 : ℝ) / 5)) ^ 2 = Φ ^ ((8 : ℝ) / 5) := by
    rw [← Real.rpow_natCast (Φ ^ ((4:ℝ)/5)) 2, ← Real.rpow_mul (le_of_lt hΦpos)]; norm_num
  have hRsq : ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2
      = (rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [hL85, hRsq] at hsq
  -- smooth_refinement (cast): rad^2 · L ≤ Φ · P^2.
  have hsmooth : (rad (F k n) : ℝ) ^ 2 * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 := by
    rw [hΦ]; exact_mod_cast smooth_refinement hn hPow
  -- Combine: Φ^{8/5} · L ≤ rad^2 · k^{2k} · L = (rad^2 · L) · k^{2k} ≤ Φ · P^2 · k^{2k}.
  have hk2kpos : (0 : ℝ) < (k : ℝ) ^ (2 * k) := by positivity
  have hstep : Φ ^ ((8 : ℝ) / 5) * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    calc Φ ^ ((8 : ℝ) / 5) * (L k : ℝ)
        ≤ ((rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) * (L k : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (le_of_lt hLpos)
      _ = ((rad (F k n) : ℝ) ^ 2 * (L k : ℝ)) * (k : ℝ) ^ (2 * k) := by ring
      _ ≤ (Φ * (P k : ℝ) ^ 2) * (k : ℝ) ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hsmooth (le_of_lt hk2kpos)
      _ = Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by ring
  -- Divide by Φ:  Φ^{3/5} · L ≤ P^2 · k^{2k}.   (Φ^{8/5} = Φ^{3/5}·Φ.)
  have hΦsplit : Φ ^ ((8 : ℝ) / 5) = Φ ^ ((3 : ℝ) / 5) * Φ := by
    rw [show (8 : ℝ)/5 = (3:ℝ)/5 + 1 by norm_num, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hstep
  have hdiv : Φ ^ ((3 : ℝ) / 5) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    have h : Φ ^ ((3 : ℝ) / 5) * (L k : ℝ) * Φ ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by
      calc Φ ^ ((3 : ℝ) / 5) * (L k : ℝ) * Φ
          = Φ ^ ((3 : ℝ) / 5) * Φ * (L k : ℝ) := by ring
        _ ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := hstep
        _ = (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by ring
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k:  (n^k)^{3/5}·L ≤ Φ^{3/5}·L ≤ P^2·k^{2k}.
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hnpow : ((n : ℝ) ^ k) ^ ((3 : ℝ) / 5) ≤ Φ ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow hnk_nonneg hFlow (by norm_num)
  have hkey : ((n : ℝ) ^ k) ^ ((3 : ℝ) / 5) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) :=
    le_trans (mul_le_mul_of_nonneg_right hnpow (le_of_lt hLpos)) hdiv
  -- Raise to the 5th power:  n^{3k} · L^5 ≤ (P^2 · k^{2k})^5 = (k^{2k})^5 · P^{10}.
  have hLHS5_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ ((3 : ℝ) / 5) * (L k : ℝ) := by positivity
  have hpow5 : (((n : ℝ) ^ k) ^ ((3 : ℝ) / 5) * (L k : ℝ)) ^ 5
      ≤ ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ 5 :=
    pow_le_pow_left₀ hLHS5_nonneg hkey 5
  -- Simplify the 5th power of the left side:  (n^k)^{3/5·5} · L^5 = n^{3k} · L^5.
  have hLHS : (((n : ℝ) ^ k) ^ ((3 : ℝ) / 5) * (L k : ℝ)) ^ 5
      = (n : ℝ) ^ (3 * k) * (L k : ℝ) ^ 5 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ ((3:ℝ)/5)) 5, ← Real.rpow_mul hnk_nonneg,
      ← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt (by positivity : (0:ℝ) < (n:ℝ))),
      ← Real.rpow_natCast (n : ℝ) (3 * k)]
    · congr 1; push_cast; ring
  have hRHS : ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ 5
      = ((k : ℝ) ^ (2 * k)) ^ 5 * (P k : ℝ) ^ 10 := by
    rw [mul_pow]; ring
  rw [hLHS, hRHS] at hpow5
  exact hpow5

/-- **Headline (g = 5 threshold).** Under `BlockRadLB5` (the genuine abc input, the only hypothesis
here), for `k ≥ 5`, if `n` exceeds the threshold `(k^{2k})^5 · P^{10} < n^{3k} · L^5`, then `F k n`
is **not powerful**. The `g = 5` ingredient `4/5 > 2/3` makes this `n > k^{5/3 + o(1)}`. -/
theorem not_powerful_g5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n)
    (hthr : ((k ^ (2 * k)) ^ 5 * P k ^ 10 : ℕ) < n ^ (3 * k) * L k ^ 5) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hmaster := master_ineq5 hBlock5 hk hn hPow
  have hcast : (((k ^ (2 * k)) ^ 5 * P k ^ 10 : ℕ) : ℝ) < ((n ^ (3 * k) * L k ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast hthr
  push_cast at hcast hmaster
  linarith [hcast, hmaster]

/-! ## PART B — the small-`n` (Bertrand) input -/

/-- **Small-`n` lemma (unconditional, via Bertrand).** For `2 ≤ k`, `1 ≤ n`, and `n ≤ k`, the
product `F k n` is **not powerful**.

Write `N = n + k - 1` (the top of the block, the largest factor). Applying Mathlib's Bertrand
postulate (`Nat.exists_prime_lt_and_le_two_mul`) at `m = N / 2` (which is `≥ 1` since `N ≥ 2`) yields
a prime `p` with `N / 2 < p ≤ 2 ⌊N/2⌋ ≤ N`. Hence:

* **Upper / single-occurrence:** `2p > 2 ⌊N/2⌋ ≥ N - 1`, so `2p > N - 1`, giving `2p > N` (as
  `2p ≥ N/2·2 + 2 > N`). Thus the only multiple of `p` in `[1, N]` that is itself a block factor is
  `p` (any other multiple is `≥ 2p > N`), and `p^2 ≥ (N/2+1)^2 > N` too.
* **Lower / membership:** `p > N / 2 = (n + k - 1) / 2 ≥ (n + n - 1) / 2 ≥ n - 1` (using `n ≤ k`),
  so `p ≥ n`; and `p ≤ N = n + k - 1`. Hence `p = n + i₀` for some `i₀ < k`: `p` is a **term**.

Then `v_p(F k n) = ∑_{i<k} v_p(n+i) = v_p(p) = 1` (every other factor `< 2p` is not a multiple of
`p`), so `p ∣ F` but `p^2 ∤ F`, contradicting powerfulness. The single occurrence comes from `2p > N`,
not from `p > k`. -/
theorem upper_half_prime_not_powerful {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (hnk : n ≤ k) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hFne : F k n ≠ 0 := F_ne_zero hn
  -- N = n + k - 1, the largest factor of the block.
  set N : ℕ := n + k - 1 with hN
  have hN2 : 2 ≤ N := by omega
  have hm1 : N / 2 ≠ 0 := by omega
  -- Bertrand at m = N/2:  a prime p with N/2 < p ≤ 2·(N/2).
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) hm1
  -- 2·(N/2) ≤ N, so p ≤ N.
  have h2half_le : 2 * (N / 2) ≤ N := by omega
  have hpN : p ≤ N := le_trans hple h2half_le
  -- 2p > N:  p ≥ N/2 + 1 ⇒ 2p ≥ 2(N/2) + 2 ≥ N + 1 > N.
  have h2half_ge : N ≤ 2 * (N / 2) + 1 := by omega
  have h2p : N < 2 * p := by omega
  -- p ≥ n:  p > N/2 = (n+k-1)/2 and n ≤ k give N/2 ≥ n - 1, so p ≥ n.
  have hhalf_ge : n - 1 ≤ N / 2 := by
    rw [hN]
    have : 2 * (n - 1) ≤ n + k - 1 := by omega
    omega
  have hpn : n ≤ p := by omega
  -- p is a term:  n ≤ p ≤ n + k - 1, so p = n + i₀ with i₀ < k.
  have hi0lt : p - n < k := by omega
  have hterm : n + (p - n) = p := by omega
  set i₀ : ℕ := p - n with hi0
  -- v_p(F k n) = ∑_{i<k} v_p(n+i).
  have hfac : (F k n).factorization p = ∑ i ∈ Finset.range k, (n + i).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro i _; omega)]
    rw [Finset.sum_apply']
  -- Every summand with i ≠ i₀ vanishes:  p ∤ (n+i), since 0 < n+i ≤ N < 2p forces n+i = p.
  have hsingle : (∑ i ∈ Finset.range k, (n + i).factorization p)
      = (n + i₀).factorization p := by
    rw [Finset.sum_eq_single i₀]
    · intro i hi hii₀
      have hik : i < k := Finset.mem_range.mp hi
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpi
      -- p ∣ n+i, 0 < n+i ≤ N < 2p ⇒ n+i = p ⇒ i = i₀.
      have hni_pos : 0 < n + i := by omega
      have hni_le : n + i ≤ N := by omega
      have hni_lt : n + i < 2 * p := by omega
      -- p ∣ n+i with n+i < 2p and n+i > 0 ⇒ n+i = p.
      obtain ⟨c, hc⟩ := hpi
      have hc1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with hclt2 | hcge2
        · -- c ∈ {0, 1};  c = 0 gives n+i = 0, contradicting n+i > 0.
          interval_cases c
          · omega
          · rfl
        · -- c ≥ 2 ⇒ n+i = p*c ≥ 2p, contradiction with n+i < 2p.
          exfalso
          have h2pc : 2 * p ≤ p * c :=
            calc 2 * p = p * 2 := by ring
              _ ≤ p * c := Nat.mul_le_mul_left p hcge2
          omega
      rw [hc1, mul_one] at hc
      -- n+i = p = n+i₀ ⇒ i = i₀.
      have : n + i = n + i₀ := by rw [hc, ← hterm]
      omega
    · intro hcon; exact absurd (Finset.mem_range.mpr hi0lt) hcon
  -- v_p(n+i₀) = v_p(p) = 1.
  have hvterm : (n + i₀).factorization p = 1 := by
    rw [hterm, Nat.Prime.factorization_self hp]
  have hvF : (F k n).factorization p = 1 := by rw [hfac, hsingle, hvterm]
  -- p ∣ F (via the i₀-th term), so powerfulness gives p² ∣ F, i.e. v_p(F) ≥ 2.  Contradiction.
  have hpF : p ∣ F k n := by
    have hmem : i₀ ∈ Finset.range k := Finset.mem_range.mpr hi0lt
    have hdvd : (n + i₀) ∣ F k n := by unfold F; exact Finset.dvd_prod_of_mem _ hmem
    rwa [hterm] at hdvd
  have hp2F : p ^ 2 ∣ F k n := hPow p hp hpF
  have hge2 : 2 ≤ (F k n).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hFne).mp hp2F
  omega

/-! ## PART C — the honest `g = 5` finiteness and the abstract splice machine -/

/-- The explicit `g = 5` finiteness bound `M k = (k^{2k})^5 · P k^{10}`. -/
def Msplice (k : ℕ) : ℕ := (k ^ (2 * k)) ^ 5 * P k ^ 10

/-- Explicit bound form of the `g = 5` deduction: a powerful `F k n` (with `k ≥ 5`,
`n ≥ 1`) forces `n ≤ Msplice k`. The reusable core; `g5_finiteness` is the corollary. -/
theorem powerful_bound_g5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    n ≤ Msplice k := by
  by_contra hnot
  have hcon : Msplice k < n := by omega
  have hthr : (Msplice k : ℕ) < n ^ (3 * k) * L k ^ 5 := by
    have hn3k : 1 ≤ n ^ (3 * k) := Nat.one_le_pow _ _ (by omega)
    have hL1 : 1 ≤ L k ^ 5 := Nat.one_le_pow _ _ (L_pos k)
    calc Msplice k
        < n := hcon
      _ ≤ n ^ (3 * k) := Nat.le_self_pow (by omega) n
      _ ≤ n ^ (3 * k) * L k ^ 5 := Nat.le_mul_of_pos_right _ (by omega)
  exact not_powerful_g5 hBlock5 hk hn (by rw [Msplice] at hthr; exact hthr) hPow

/-- **Honest `g = 5` finiteness (from `BlockRadLB5` ALONE).** For `k ≥ 5`, under the single analytic
hypothesis `BlockRadLB5`, the set of `n ≥ 1` with `F k n` powerful is **finite**: every such `n`
satisfies the explicit bound `n ≤ Msplice k = (k^{2k})^5 · P k^{10}`. Corollary of
`powerful_bound_g5`; involves no BHP, no Bertrand, and no Mertens — just `BlockRadLB5`. -/
theorem g5_finiteness (hBlock5 : BlockRadLB5) {k : ℕ} (hk : 5 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (Msplice k))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  exact powerful_bound_g5 hBlock5 hk hn.1 hn.2

/-- **Ranged prime-in-block input.** `PrimeInBlockOnRange Range` says: on the range `Range k n`
(with `k ≥ 3`, `1 ≤ n`), the block `[n, n+k-1]` contains a prime `p > k` that is a term `n + i` of the
block. This replaces the old too-strong global `BHP`: it only asks for a prime on whatever range
`Range` it is instantiated at (e.g. the genuine Baker–Harman–Pintz range `n ≤ k^{40/21}`), never in
"every" block. It enters as a hypothesis; Baker–Harman–Pintz is NOT formalized. -/
def PrimeInBlockOnRange (Range : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → Range k n →
    ∃ p, p.Prime ∧ k < p ∧ ∃ i < k, n + i = p

/-- **Ranged prime deduction.** Given a ranged prime input `PrimeInBlockOnRange Range`, for `k ≥ 3`,
`1 ≤ n`, and `hR : Range k n`, the product `F k n` is not powerful: the prime `p > k` supplied on the
range is a term of the block, and `prime_in_block_not_powerful` (TaoPoint) rules out powerfulness. -/
theorem prime_range_not_powerful {Range : ℕ → ℕ → Prop}
    (hPrime : PrimeInBlockOnRange Range) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hR : Range k n) : ¬ Powerful (F k n) := by
  obtain ⟨p, hp, hpk, hmem⟩ := hPrime k n hk hn hR
  exact prime_in_block_not_powerful hp hpk hn hmem

/-- **Coverage of the three ranges.** `CoversAll Mid High` says every `(k, n)` with `k ≥ 3`, `1 ≤ n`
falls into the small range `n ≤ k`, the middle range `Mid k n`, or the high range `High k n`. On the
intended instantiation, `Mid` = BHP range, `High` = Mertens-sharpened `g = 5` range, and coverage is
the inequality `5/3 < 40/21` (kept external). -/
def CoversAll (Mid High : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → n ≤ k ∨ Mid k n ∨ High k n

/-- **The abstract splice machine — the honest no-gap architecture.** Parametric in two range
predicates `Mid High`. Given:

* `hCover : CoversAll Mid High` — every `(k, n)` is small (`n ≤ k`), middle (`Mid`), or high (`High`);
* `hMid : PrimeInBlockOnRange Mid` — a prime `p > k` term of the block on the middle range;
* `hHigh : ∀ k n, 3 ≤ k → 1 ≤ n → High k n → ¬ Powerful (F k n)` — non-powerfulness on the high range;

then `¬ Powerful (F k n)` for **every** `(k, n)` with `k ≥ 3`, `1 ≤ n`. The small range is discharged
unconditionally by `upper_half_prime_not_powerful` (Bertrand); the middle range by
`prime_range_not_powerful`; the high range by the supplied `hHigh`. Baker–Harman–Pintz, Mertens, and
the exact exponents live entirely inside the three premises — Lean never assumes them, so it never
assumes "a prime in every block". For `k ≥ 5`, instantiating `Mid` = BHP range and `High` =
Mertens-sharpened `g = 5` range, with `hHigh` supplied by `not_powerful_g5`, gives the clean
Pandey-free no-gap splice, whose analytic inputs remain external. -/
theorem abstract_splice_no_counterexamples {Mid High : ℕ → ℕ → Prop}
    (hCover : CoversAll Mid High)
    (hMid : PrimeInBlockOnRange Mid)
    (hHigh : ∀ k n, 3 ≤ k → 1 ≤ n → High k n → ¬ Powerful (F k n))
    {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) : ¬ Powerful (F k n) := by
  rcases hCover k n hk hn with hsmall | hmid | hhigh
  · exact upper_half_prime_not_powerful (by omega) hn hsmall
  · exact prime_range_not_powerful hMid hk hn hmid
  · exact hHigh k n hk hn hhigh

end  -- noncomputable section

end Erdos137
