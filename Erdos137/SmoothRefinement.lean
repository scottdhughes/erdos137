import Erdos137.JointFiniteness

namespace Erdos137

/-!
# Erdős Problem #137: the smooth-part radical refinement and the sharpened threshold

`Erdos137/JointFiniteness.lean` derives the threshold `n > k^6` from the crude powerful bound
`rad(F k n)^2 ≤ F k n` (`powerful_rad_sq_le`). That bound is wasteful: the `k`-smooth part of a
powerful `F k n` is itself very powerful, and its radical is bounded by the primorial of `k`.

This file sharpens the powerful radical bound for the consecutive product `F k n`. Write
`F = S · R` where

* `S = ∏_{p < k} p^{v_p(F)}` is the `k`-smooth part (primes below `k`), and
* `R = ∏_{p ≥ k} p^{v_p(F)}` is the rough part (primes at least `k`).

Two primorial-type quantities measure `S`:

* `P k = ∏_{p ∈ primesBelow k} p` (the primorial of `k`, primes `< k`), and
* `L k = ∏_{p ∈ primesBelow k} p ^ (k / p)`.

For `n ≥ 1` and a **powerful** `F k n` we prove the refined bound

  `smooth_refinement :  rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2`.

The three ingredients:

* `rad(S)^2 ≤ P^2`: the smooth primes dividing `F` are a subset of `primesBelow k`, so
  `rad(S) = ∏_{p|F, p<k} p ∣ ∏_{p<k} p = P` (`rad_smooth_le_P`).
* `rad(R)^2 ≤ R`: each prime `p ≥ k` dividing a powerful `F` has `v_p(F) ≥ 2`, so `p^2 ≤ p^{v_p}`
  (`rough_sq_le`). (Powerfulness alone gives `v_p ≥ 2`; we do not need that `p ≥ k` divides only
  one factor.)
* `L ∣ S`, hence `L ≤ S`: among the `k` consecutive integers `n, …, n+k-1` at least `⌊k/p⌋` are
  divisible by `p`, so `v_p(F) ≥ ⌊k/p⌋ = v_p(L)` for every prime `p < k` (`L_dvd_F`,
  `L_le_smooth`).

Then `rad(F)^2 = rad(S)^2 · rad(R)^2 ≤ P^2 · R = P^2 · F / S ≤ (P^2 / L) · F`, i.e.
`rad(F)^2 · L ≤ F · P^2`.

Since `P k ≤ 4^k` (`P_le_4_pow`, from Mathlib's `primorial_le_4_pow`) and `L k = (k!)^{1-o(1)}`,
the ratio `(P^2 / L)^3` is `k^{-3k + o(k)}`, so the smooth gain cubically sharpens the threshold.
The headline `not_powerful_of_large'` is stated in the exact, fully-proved integer form

  `(k^{2k})^3 · P^6 < n^k · L^3  ⟹  ¬ Powerful (F k n)`;

feeding in the Mertens lower bound `log L = k log k − O(k)` (which is not in Mathlib and so is not
formalized here) turns this threshold into `n > k^{3 + o(1)}`, cubically below the crude `k^6`.
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## The primorial-type quantities `P k` and `L k` -/

/-- `P k = ∏_{p ∈ primesBelow k} p` — the product of the primes `< k` (the primorial of `k`). -/
def P (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p

/-- `L k = ∏_{p ∈ primesBelow k} p ^ (k / p)` — the smooth-part lower bound (`L ∣ k!` by Legendre,
`L = (k!)^{1-o(1)}`). -/
def L (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p ^ (k / p)

lemma P_pos (k : ℕ) : 1 ≤ P k :=
  Finset.one_le_prod' fun p hp => (Nat.prime_of_mem_primesBelow hp).one_le

lemma L_pos (k : ℕ) : 1 ≤ L k :=
  Finset.one_le_prod' fun p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos

lemma L_ne_zero (k : ℕ) : L k ≠ 0 := Nat.one_le_iff_ne_zero.mp (L_pos k)

/-- `P k ≤ 4 ^ k` (Mathlib's `primorial_le_4_pow`; `primesBelow k` are the primes `≤ k - 1`,
a subset of the primes counted by `primorial k`). -/
lemma P_le_4_pow (k : ℕ) : P k ≤ 4 ^ k := by
  have hsub : Nat.primesBelow k ⊆ {p ∈ Finset.range (k + 1) | p.Prime} := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hdvd : P k ∣ primorial k := by
    unfold P primorial
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  calc P k ≤ primorial k := Nat.le_of_dvd (primorial_pos k) hdvd
    _ ≤ 4 ^ k := primorial_le_4_pow k

/-! ## The smooth/rough split of `F k n` -/

/-- The smooth part `S k n = ∏_{p | F, p < k} p ^ v_p(F)`. -/
def Ssmooth (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (· < k), p ^ (F k n).factorization p

/-- The rough part `R k n = ∏_{p | F, ¬ p < k} p ^ v_p(F)`. -/
def Rrough (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p ^ (F k n).factorization p

/-- `S · R = F` for `n ≥ 1`. -/
lemma Ssmooth_mul_Rrough {k n : ℕ} (hn : 1 ≤ n) : Ssmooth k n * Rrough k n = F k n := by
  unfold Ssmooth Rrough
  rw [Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self (F_ne_zero hn)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

lemma Ssmooth_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ Ssmooth k n :=
  Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

lemma Rrough_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ Rrough k n :=
  Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

/-! ## Bound on the smooth radical: `rad(S)^2 ≤ P^2` -/

/-- `∏_{p | F, p < k} p ∣ P k`: the smooth prime factors are a subset of `primesBelow k`. -/
lemma smooth_rad_dvd_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ∣ P k := by
  unfold P
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [Nat.mem_primesBelow]
  exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩

/-- `∏_{p | F, p < k} p ≤ P k`. -/
lemma smooth_rad_le_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ≤ P k :=
  Nat.le_of_dvd (P_pos k) smooth_rad_dvd_P

/-! ## Bound on the rough part: `∏_{p | F, ¬ p<k} p^2 ≤ R` (powerful) -/

/-- For powerful `F` (`≠ 0`), `∏_{p|F, ¬p<k} p^2 ≤ R k n`: each such prime has `v_p(F) ≥ 2`. -/
lemma rough_sq_le {k n : ℕ} (hF : F k n ≠ 0) (hP : Powerful (F k n)) :
    (∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p) ^ 2 ≤ Rrough k n := by
  unfold Rrough
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  have hpdvd : p ∣ F k n := Nat.dvd_of_mem_primeFactors hp.1
  have h2 : p ^ 2 ∣ F k n := hP p hpp hpdvd
  have hle : 2 ≤ (F k n).factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hpp hF).mp h2
  exact Nat.pow_le_pow_right hpp.pos hle

/-! ## The smooth lower bound: `L ∣ S` and `L ≤ S`

We need `v_p(F) ≥ ⌊k/p⌋` for every prime `p < k`. Among the `k` consecutive integers
`n, …, n+k-1` (the multiset `(n-1, n-1+k]` shifted), at least `⌊k/p⌋` are divisible by `p`, and
each such factor contributes at least `1` to `v_p(F)`. -/

/-- The count of multiples of `p` among the `k` consecutive integers `n, …, n+k-1` is at least
`⌊k/p⌋`. Stated via the exact `Ioc` count: `#{x ∈ (n-1, n-1+k] | p ∣ x} = (n-1+k)/p − (n-1)/p ≥ k/p`. -/
lemma div_le_factorization_F {k n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    k / p ≤ (F k n).factorization p := by
  -- v_p(F) = ∑_{i<k} v_p(n+i) ≥ #{i<k | p ∣ n+i} = #{x ∈ (n-1, n-1+k] | p∣x} ≥ k/p.
  set D : Finset ℕ := (Finset.range k).filter (fun i => p ∣ (n + i)) with hD
  -- Lower bound: each multiple contributes ≥ 1.
  have hfac : (F k n).factorization p = ∑ i ∈ Finset.range k, (n + i).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro i _; omega)]
    rw [Finset.sum_apply']
  have hcount_le : #D ≤ (F k n).factorization p := by
    rw [hfac]
    calc #D = ∑ i ∈ D, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ D, (n + i).factorization p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hD, Finset.mem_filter] at hi
          have hne : n + i ≠ 0 := by omega
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp hne).mp (by simpa using hi.2)
      _ ≤ ∑ i ∈ Finset.range k, (n + i).factorization p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro i _ _; positivity)
  -- Relate #D to the Ioc count of multiples.
  have hbij : #D = #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} := by
    apply Finset.card_bij (fun i _ => n + i)
    · intro i hi
      rw [hD, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hi.2⟩
    · intro i hi j hj h; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxdvd⟩ := hx
      refine ⟨x - n, ?_, ?_⟩
      · rw [hD, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [show n + (x - n) = x by omega]; exact hxdvd
      · omega
  have hcount : #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} = (n - 1 + k) / p - (n - 1) / p :=
    Ioc_dvd_count (n - 1) (n - 1 + k) p (by omega)
  -- ⌊(a+k)/p⌋ − ⌊a/p⌋ ≥ ⌊k/p⌋.
  have hkey : k / p ≤ (n - 1 + k) / p - (n - 1) / p := by
    have h1 : (n - 1) / p + k / p ≤ (n - 1 + k) / p := Nat.add_div_le_add_div (n - 1) k p
    omega
  omega

/-- `L k ∣ F k n` for `n ≥ 1`: `v_p(L) = ⌊k/p⌋ ≤ v_p(F)` for every prime `p < k`. -/
lemma L_dvd_F {k n : ℕ} (hn : 1 ≤ n) : L k ∣ F k n := by
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)]
  intro p
  rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
  rw [Nat.factorization_prod (fun q hq => by
    have := (Nat.prime_of_mem_primesBelow hq).pos
    positivity)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hsingle : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p)
        = (p ^ (k / p)).factorization p :=
      Finset.sum_eq_single p
        (fun q hq hqp => by
          have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
          rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hqp])
        (fun h => absurd hp h)
    rw [hsingle, Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
    exact div_le_factorization_F hn hpp
  · have hzero : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]
    rw [hzero]; exact Nat.zero_le _

/-- `L k ≤ S k n` (the smooth part): `L ∣ F` and `L`'s primes are exactly the smooth primes, so in
fact `L ∣ S`; we only need `L ≤ S`. -/
lemma L_le_smooth {k n : ℕ} (hn : 1 ≤ n) : L k ∣ Ssmooth k n := by
  -- L ∣ F and all prime factors of L are < k, so L ∣ S (the < k part of F).
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (Nat.one_le_iff_ne_zero.mp (Ssmooth_pos hn))]
  intro p
  have hLdvdF : L k ∣ F k n := L_dvd_F hn
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hplt : p < k := Nat.lt_of_mem_primesBelow hp
    -- v_p(L) ≤ v_p(F) = v_p(S) since p < k.
    have hvLF : (L k).factorization p ≤ (F k n).factorization p :=
      (Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)).mpr hLdvdF p
    have hvFS : (F k n).factorization p ≤ (Ssmooth k n).factorization p := by
      by_cases hpdvd : p ∈ (F k n).primeFactors
      · unfold Ssmooth
        rw [Nat.factorization_prod (fun q hq => by
          have := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)).pos; positivity)]
        rw [Finset.sum_apply']
        have hmem : p ∈ (F k n).primeFactors.filter (· < k) := by
          rw [Finset.mem_filter]; exact ⟨hpdvd, hplt⟩
        rw [Finset.sum_eq_single p
              (fun q hq hqp => by
                have hqp' : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)
                rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hqp])
              (fun h => absurd hmem h)]
        rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
      · -- p ∤ F ⇒ v_p(F) = 0
        rw [Nat.factorization_eq_zero_of_not_dvd]
        · exact Nat.zero_le _
        · intro hdvd; exact hpdvd (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, F_ne_zero hn⟩)
    exact le_trans hvLF hvFS
  · have hzero : (L k).factorization p = 0 := by
      rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
      rw [Nat.factorization_prod (fun q hq => by
        have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
      rw [Finset.sum_apply']
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]
    rw [hzero]; exact Nat.zero_le _

/-! ## `rad (F k n)` factored through the smooth/rough split -/

/-- `rad (F k n) = (∏_{p|F, p<k} p) · (∏_{p|F, ¬p<k} p)`. -/
lemma rad_smooth_rough_split (k n : ℕ) :
    rad (F k n)
      = (∏ p ∈ (F k n).primeFactors.filter (· < k), p)
        * (∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p) := by
  unfold rad
  rw [Nat.support_factorization]
  rw [Finset.prod_filter_mul_prod_filter_not]

/-! ## The smooth refinement -/

/-- **Smooth-part radical refinement.** For `n ≥ 1` and a **powerful** `F k n`,
`rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2`. Equivalently `rad(F)^2 ≤ (P^2 / L) · F`; this sharpens
the crude `rad(F)^2 ≤ F` (`powerful_rad_sq_le`) by the smooth gain `L`. -/
theorem smooth_refinement {k n : ℕ} (hn : 1 ≤ n) (hP : Powerful (F k n)) :
    rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2 := by
  have hF : F k n ≠ 0 := F_ne_zero hn
  set sm : ℕ := ∏ p ∈ (F k n).primeFactors.filter (· < k), p with hsm
  set rg : ℕ := ∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p with hrg
  -- rad(F)^2 = sm^2 * rg^2
  have hradsq : rad (F k n) ^ 2 = sm ^ 2 * rg ^ 2 := by
    rw [rad_smooth_rough_split, mul_pow]
  -- sm^2 ≤ P^2
  have hsmP : sm ^ 2 ≤ P k ^ 2 := Nat.pow_le_pow_left smooth_rad_le_P 2
  -- rg^2 ≤ R
  have hrgR : rg ^ 2 ≤ Rrough k n := rough_sq_le hF hP
  -- L ∣ S, so L ≤ S
  have hLS : L k ≤ Ssmooth k n := Nat.le_of_dvd (Ssmooth_pos hn) (L_le_smooth hn)
  -- L * R ≤ S * R = F
  have hLR_F : L k * Rrough k n ≤ F k n := by
    calc L k * Rrough k n ≤ Ssmooth k n * Rrough k n :=
            Nat.mul_le_mul_right _ hLS
      _ = F k n := Ssmooth_mul_Rrough hn
  -- Assemble:  rad(F)^2 * L = sm^2 * (rg^2 * L) ≤ P^2 * (R * L) ≤ P^2 * F.
  calc rad (F k n) ^ 2 * L k
      = sm ^ 2 * (rg ^ 2 * L k) := by rw [hradsq]; ring
    _ ≤ P k ^ 2 * (Rrough k n * L k) := by
        apply Nat.mul_le_mul hsmP
        exact Nat.mul_le_mul_right _ hrgR
    _ = P k ^ 2 * (L k * Rrough k n) := by ring
    _ ≤ P k ^ 2 * F k n := Nat.mul_le_mul_left _ hLR_F
    _ = F k n * P k ^ 2 := by ring

/-! ## The sharpened threshold

Feeding `smooth_refinement` (`rad(F)^2 · L ≤ F · P^2`) into the block chain
`Φ^{2/3} ≤ ∏ rad ≤ rad(F) · W ≤ rad(F) · k^k` (with `W ≤ k^k`, `Φ = F k n`) in place of the crude
`rad(F)^2 ≤ Φ` gives, after squaring and dividing by `Φ`,

  `Φ^{1/3} · L ≤ k^{2k} · P^2`,

equivalently (cubing, and using `Φ ≥ n^k`)

  `n^k · L^3 ≤ k^{6k} · P^6`.

This is the **smooth-refined master inequality** (`master_ineq`); the crude route gave only
`n^k ≤ k^{6k}` (i.e. `n ≤ k^6`). The new inequality has the extra `L^3` on the left — the smooth
gain — so the threshold drops from `k^6` to `k^6 · (P^2 / L)^3 = k^{3 + o(1)}`. -/

/-- **Smooth-refined master inequality.** Under `BlockRadLB`, for `k ≥ 3` and a powerful `F k n`
with `n ≥ 1`:  `n^k · L k ^ 3 ≤ (k ^ (2 * k)) ^ 3 * P k ^ 6`. The left factor `L k ^ 3` is the
smooth gain absent from the crude `n^k ≤ (k^{2k})^3 = k^{6k}` route. -/
theorem master_ineq (hBlock : BlockRadLB) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ k * (L k : ℝ) ^ 3 ≤ ((k : ℝ) ^ (2 * k)) ^ 3 * (P k : ℝ) ^ 6 := by
  have hkpos : 0 < k := by omega
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  have hLpos : (0 : ℝ) < (L k : ℝ) := by exact_mod_cast L_pos k
  -- Block chain: Φ^{2/3} ≤ ∏rad ≤ rad·W ≤ rad·k^k.
  have hblk := hBlock k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / 3), rad (F 3 (n + 3 * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * (W k n : ℝ) := by
    rw [hPrd]; exact_mod_cast rad_triples_le hn
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hW : (W k n : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast W_le_pow hn
  have hchain : Φ ^ ((2 : ℝ) / 3) ≤ (rad (F k n) : ℝ) * (k : ℝ) ^ k :=
    le_trans (le_trans hblk hdecomp) (mul_le_mul_of_nonneg_left hW hradpos)
  -- Square: Φ^{4/3} ≤ rad^2 · k^{2k}.
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ ((2 : ℝ) / 3)) ^ 2 ≤ ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hL43 : (Φ ^ ((2 : ℝ) / 3)) ^ 2 = Φ ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (Φ ^ ((2:ℝ)/3)) 2, ← Real.rpow_mul (le_of_lt hΦpos)]; norm_num
  have hRsq : ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2
      = (rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [hL43, hRsq] at hsq
  -- smooth_refinement (cast): rad^2 · L ≤ Φ · P^2.
  have hsmooth : (rad (F k n) : ℝ) ^ 2 * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 := by
    rw [hΦ]; exact_mod_cast smooth_refinement hn hPow
  -- Combine: Φ^{4/3} · L ≤ rad^2 · k^{2k} · L = (rad^2 · L) · k^{2k} ≤ Φ · P^2 · k^{2k}.
  have hk2kpos : (0 : ℝ) < (k : ℝ) ^ (2 * k) := by positivity
  have hstep : Φ ^ ((4 : ℝ) / 3) * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    calc Φ ^ ((4 : ℝ) / 3) * (L k : ℝ)
        ≤ ((rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) * (L k : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (le_of_lt hLpos)
      _ = ((rad (F k n) : ℝ) ^ 2 * (L k : ℝ)) * (k : ℝ) ^ (2 * k) := by ring
      _ ≤ (Φ * (P k : ℝ) ^ 2) * (k : ℝ) ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hsmooth (le_of_lt hk2kpos)
      _ = Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by ring
  -- Divide by Φ:  Φ^{1/3} · L ≤ P^2 · k^{2k}.   (Φ^{4/3} = Φ^{1/3}·Φ.)
  have hΦsplit : Φ ^ ((4 : ℝ) / 3) = Φ ^ ((1 : ℝ) / 3) * Φ := by
    rw [show (4 : ℝ)/3 = (1:ℝ)/3 + 1 by norm_num, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hstep
  have hdiv : Φ ^ ((1 : ℝ) / 3) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    have h : Φ ^ ((1 : ℝ) / 3) * (L k : ℝ) * Φ ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by
      calc Φ ^ ((1 : ℝ) / 3) * (L k : ℝ) * Φ
          = Φ ^ ((1 : ℝ) / 3) * Φ * (L k : ℝ) := by ring
        _ ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := hstep
        _ = (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by ring
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k:  n^{k/3}·L ≤ Φ^{1/3}·L ≤ P^2·k^{2k}.
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hncube : ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) ≤ Φ ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hnk_nonneg hFlow (by norm_num)
  have hkey : ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) :=
    le_trans (mul_le_mul_of_nonneg_right hncube (le_of_lt hLpos)) hdiv
  -- Cube both sides:  n^k · L^3 ≤ (P^2 · k^{2k})^3 = (k^{2k})^3 · P^6.
  have hLHScube_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) * (L k : ℝ) := by positivity
  have hcubed : (((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) * (L k : ℝ)) ^ 3
      ≤ ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ 3 :=
    pow_le_pow_left₀ hLHScube_nonneg hkey 3
  -- Simplify the cube of the left side:  (n^k)^{1/3·3} · L^3 = n^k · L^3.
  have hLHS : (((n : ℝ) ^ k) ^ ((1 : ℝ) / 3) * (L k : ℝ)) ^ 3 = (n : ℝ) ^ k * (L k : ℝ) ^ 3 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hnk_nonneg]
    norm_num
  have hRHS : ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ 3 = ((k : ℝ) ^ (2 * k)) ^ 3 * (P k : ℝ) ^ 6 := by
    rw [mul_pow]; ring
  rw [hLHS, hRHS] at hcubed
  exact hcubed

/-- **Sharpened headline (smooth-refined threshold).** Under `BlockRadLB` (the genuine abc input,
the only hypothesis), for `k ≥ 3`, if `n` exceeds the smooth-refined threshold
`(k^{2k})^3 · P^6 < n^k · L^3`, then `F k n` is **not powerful**.

The crude route (`not_powerful_of_large`) needs `n^k > (k^{2k})^3 = k^{6k}`, i.e. `n > k^6`. Here
the `L^3` smooth gain on the right means the same conclusion follows once
`n^k · L^3 > (k^{2k})^3 · P^6`. Since `L = (k!)^{1 - o(1)}` and `P ≤ 4^k`, the ratio `(P^2/L)^3` is
`k^{-3k + o(k)}`, so this threshold is `n > k^{3 + o(1)}` — cubically sharper than `k^6`. -/
theorem not_powerful_of_large' (hBlock : BlockRadLB) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n)
    (hthr : ((k ^ (2 * k)) ^ 3 * P k ^ 6 : ℕ) < n ^ k * L k ^ 3) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hmaster := master_ineq hBlock hk hn hPow
  have hcast : (((k ^ (2 * k)) ^ 3 * P k ^ 6 : ℕ) : ℝ) < ((n ^ k * L k ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hthr
  push_cast at hcast hmaster
  linarith [hcast, hmaster]

/-- **Per-fixed-`k` finiteness via the smooth-refined threshold.** For each `k ≥ 3`, under
`BlockRadLB`, the set of `n ≥ 1` with `F k n` powerful is finite: every such `n` satisfies
`n ^ k * L k ^ 3 ≤ (k ^ (2 * k)) ^ 3 * P k ^ 6`, a bounded set of `n` (as `L k ≥ 1`,
`n ^ k ≤ (k^{2k})^3 · P^6`). -/
theorem not_powerful_finite' (hBlock : BlockRadLB) {k : ℕ} (hk : 3 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic ((k ^ (2 * k)) ^ 3 * P k ^ 6))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  obtain ⟨hn1, hPow⟩ := hn
  by_contra hcon
  push_neg at hcon
  -- if n > bound then n^k·L^3 > bound, contradicting not_powerful_of_large'.
  have hthr : ((k ^ (2 * k)) ^ 3 * P k ^ 6 : ℕ) < n ^ k * L k ^ 3 := by
    have hkpos : 0 < k := by omega
    have hbase : (k ^ (2 * k)) ^ 3 * P k ^ 6 < n := hcon
    have hn1k : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
    have hL1 : 1 ≤ L k ^ 3 := Nat.one_le_pow _ _ (L_pos k)
    calc (k ^ (2 * k)) ^ 3 * P k ^ 6
        < n := hbase
      _ ≤ n ^ k := Nat.le_self_pow (by omega) n
      _ ≤ n ^ k * L k ^ 3 := Nat.le_mul_of_pos_right _ (by omega)
  exact not_powerful_of_large' hBlock hk hn1 hthr hPow

end  -- noncomputable section

end Erdos137
