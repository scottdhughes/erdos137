import Erdos137.Finiteness
import Erdos137.Base
import Erdos137.BlockFramework

namespace Erdos137

/-!
# Erdős Problem #137: per-`k` non-powerfulness via the triple tiling (g = 3 instance)

`Erdos137/Finiteness.lean` formalizes the **per-fixed-`k`** conditional result: under the
Granville–Langevin radical lower bound `RadLB k` (a consequence of the abc conjecture, taken
as a hypothesis), for each fixed `k ≥ 3` the product `F k n = n(n+1)⋯(n+k-1)` is powerful for
only finitely many `n`.

This file formalizes the **triple-tiling** route (motivated by Will Sawin's comment at
erdosproblems.com/137). Under the block radical lower bound `BlockRadLB` (the genuine abc input,
applied to the cubic triples), for `k ≥ 3` and `n > k^6` the product `F k n` is **not powerful**
(`not_powerful_of_large`); hence, for each fixed `k`, `F k n` is powerful for only finitely many
`n` (`not_powerful_finite`).

Since the unification into `Erdos137.BlockFramework`, the `g = 3` block objects (`B`, `overlap`,
`W`, `BlockRadLB`) are the **literal `g = 3` instances** of the generic framework, and the public
combinatorial lemmas (`B_eq`, `B_dvd_F`, `rad_triples_le`, `W_dvd_factorial`, `W_le_pow`, …) are thin
wrappers of their generic counterparts (`Bg_eq`, `Bg_dvd_F`, `rad_blocksg_le`, `Wg_dvd_factorial`,
`Wg_le_pow`, …). The headline theorems `not_powerful_of_large`/`not_powerful_finite` retain their
exact statements and run off those wrappers.

## The argument

* Langevin/abc gives, for the squarefree cubic `g(x) = x(x+1)(x+2)`,
  `rad(m(m+1)(m+2)) ≫_ε m^{2-ε}`. Assembled over `⌊k/3⌋` consecutive triples this is
  `∏ rad over triples ≥ (F k n)^{2/3 - ε}` (taken as `BlockRadLB`, the genuine abc input).
* `rad(F k n) = (∏ rad over triples) / W`, where `W = ∏_{p} p^{overlap − 1}` is the over-count
  from primes appearing in more than one triple.
* Each triple is 3 consecutive integers, so the `⌊k/3⌋` triples span `≤ k` consecutive integers.
  A prime `p` divides at most `⌊k/p⌋ + 1` of them, hence `overlap k n p − 1 ≤ ⌊k/p⌋ ≤ v_p(k!)`
  (Legendre's `i = 1` term). Therefore **`W ∣ k!`**, so **`W ≤ k! ≤ k^k`** — proved (generically) in
  `BlockFramework`. On the log scale `log W = ∑_{p<k} ⌊k/p⌋ log p = k log k + O(k)` (the first
  Legendre layer of `k!`, by Mertens' first theorem `∑_{p<k} (log p)/p ∼ log k`), so `W` is
  `(F k n)^{o(1)}` only for `n` super-polynomial in `k`; for `n ≍ k^A` it is `(F k n)^{1/A + o(1)}`,
  and the triple (`g = 3`) route yields the threshold `n > k^6` rather than all `n`.
* `F k n ≥ n^k` (each of the `k` factors is `≥ n`) — proved in `Base` (`pow_le_F`).
* Combine: `(F k n)^{2/3} ≤ rad(F k n) · W`, powerful ⟹ `rad(F k n)^2 ≤ F k n`, and `W ≤ k^k`,
  giving `(F k n)^{1/3} ≤ k^{2k}`. With `F k n ≥ n^k`: `n^{k/3} ≤ k^{2k} = (k^6)^{k/3}`, so
  `n ≤ k^6`. Thus `n > k^6` ⟹ `¬ Powerful (F k n)`.

## What is fully proved (no `sorry`, only Mathlib's three axioms)

* `B_eq`, `B_dvd_F`, `rad_triples_le` — the radical-of-product decomposition wrappers and inequality
  (generic forms `Bg_eq`, `Bg_dvd_F`, `rad_blocksg_le` proved in `BlockFramework`).
* `W_dvd_factorial`, `W_le_pow` — the overlap bound `W ∣ k!` / `W ≤ k^k` (`Wg_dvd_factorial`,
  `Wg_le_pow`).
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

The unconditional Erdős #137 remains open, as does abc. The crude `g = 3` triple route gives
`n > k^6`; the analogous crude `g = 4` block route gives the threshold `n > k^4`, which together with Pandey's
unconditional squarefree-value count for `n < k^{5+δ}` would give full joint `(n, k)` finiteness.
Those last two inputs are not formalized here.
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## The `g = 3` block objects as literal instances of the generic framework -/

/-- The block product `B k n = ∏_{j<⌊k/3⌋} F 3 (n+3j) = F (3⌊k/3⌋) n`: the `g = 3` instance of
the generic `Bg`. -/
def B (k n : ℕ) : ℕ := Bg 3 k n

/-- `overlap p` is the number of triples `p` divides: the `g = 3` instance of the generic
`overlapg`. -/
def overlap (k n p : ℕ) : ℕ := overlapg 3 k n p

/-- The over-count `W k n`: the `g = 3` instance of the generic `Wg`. -/
def W (k n : ℕ) : ℕ := Wg 3 k n

/-- `B k n = F (3 * (k/3)) n`. The `g = 3` instance of `Bg_eq`. -/
lemma B_eq (k n : ℕ) : B k n = F (3 * (k / 3)) n := Bg_eq (by norm_num) k n

/-- `B k n` divides `F k n`. The `g = 3` instance of `Bg_dvd_F`. -/
lemma B_dvd_F (k n : ℕ) : B k n ∣ F k n := Bg_dvd_F (by norm_num) k n

/-- `B k n ≠ 0` for `n ≥ 1`. The `g = 3` instance of `Bg_ne_zero`. -/
lemma B_ne_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : B k n ≠ 0 := Bg_ne_zero (by norm_num) hn k

/-- For `n ≥ 1` each triple `F 3 (n + 3j)` is nonzero. The `g = 3` instance of `block_ne_zero`. -/
lemma triple_ne_zero {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : F 3 (n + 3 * j) ≠ 0 :=
  block_ne_zero hn 3 j

/-- **Radical-of-product decomposition, exact form.**
`∏_j rad (F 3 (n+3j)) = rad (B k n) * W k n`. The `g = 3` instance of `rad_blocksg_decomp`. -/
theorem rad_triples_decomp {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))) = rad (B k n) * W k n :=
  rad_blocksg_decomp (by norm_num) hn

/-- `rad (B k n) ∣ rad (F k n)`. The `g = 3` instance of `rad_Bg_dvd_rad_F`. -/
lemma rad_B_dvd_rad_F {k n : ℕ} (hn : 1 ≤ n) : rad (B k n) ∣ rad (F k n) :=
  rad_Bg_dvd_rad_F (by norm_num) hn

/-- **Decomposition inequality (the usable form):**
`∏_j rad (F 3 (n+3j)) ≤ rad (F k n) * W k n`. The `g = 3` instance of `rad_blocksg_le`. -/
theorem rad_triples_le {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j))) ≤ rad (F k n) * W k n :=
  rad_blocksg_le (by norm_num) hn

/-- **Overlap bound (combinatorial core).** `overlap k n p ≤ ⌊k/p⌋ + 1` for `n ≥ 1`.
The `g = 3` instance of `overlapg_le`. -/
lemma overlap_le {k n p : ℕ} (hn : 1 ≤ n) : overlap k n p ≤ k / p + 1 :=
  overlapg_le (by norm_num) hn

/-- **Overlap product divides `k!`.** `W k n ∣ k!`. The `g = 3` instance of `Wg_dvd_factorial`. -/
theorem W_dvd_factorial {k n : ℕ} (hn : 1 ≤ n) : W k n ∣ Nat.factorial k :=
  Wg_dvd_factorial (by norm_num) hn

/-- **Overlap bound: `W k n ≤ k^k`.** The `g = 3` instance of `Wg_le_pow`. -/
theorem W_le_pow {k n : ℕ} (hn : 1 ≤ n) : W k n ≤ k ^ k :=
  Wg_le_pow (by norm_num) hn

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

/-- `BlockRadLB` is exactly the `g = 3` instance of the generic `BlockRadLBg` (the exponents
`2/3` and `(3-1)/3` agree, and the guard `3 ≤ k` matches `g ≤ k`). -/
lemma blockRadLB_iff : BlockRadLB ↔ BlockRadLBg 3 := by
  unfold BlockRadLB BlockRadLBg
  constructor
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num]
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num] at this

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
