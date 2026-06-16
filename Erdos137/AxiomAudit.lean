import Erdos137.Finiteness
import Erdos137.JointFiniteness
import Erdos137.SmoothRefinement
import Erdos137.TaoPoint

/-!
# Axiom audit

Building this file prints the axioms underlying each theorem.
Expected: only `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no
`native_decide`/`Lean.ofReduceBool`.
-/

#print axioms Erdos137.lemma_star                          -- unconditional: rad² · B2 ≤ m²
#print axioms Erdos137.powerful_rad_sq_le                  -- powerful N ⟹ rad N² ≤ N
#print axioms Erdos137.erdos137_eventually_not_powerful    -- RadLB ⟹ F k n not powerful for large n
#print axioms Erdos137.erdos137_finite                     -- RadLB ⟹ {n | powerful (F k n)} finite

-- Triple-tiling route (this file):
#print axioms Erdos137.rad_triples_decomp                  -- radical-of-product decomposition (proved)
#print axioms Erdos137.rad_triples_le                      -- decomposition inequality (proved)
#print axioms Erdos137.overlap_le                          -- overlap ≤ ⌊k/p⌋+1 (combinatorial core)
#print axioms Erdos137.W_dvd_factorial                     -- W ∣ k! (Legendre)
#print axioms Erdos137.W_le_pow                            -- overlap bound W ≤ k^k (proved)
#print axioms Erdos137.pow_le_F                            -- n^k ≤ F k n (proved)
#print axioms Erdos137.not_powerful_of_large              -- BlockRadLB → n>k^6 → ¬powerful (crude route)
#print axioms Erdos137.not_powerful_finite                -- per-k finiteness (crude route)

-- Smooth-part radical refinement (this file): sharpened threshold.
#print axioms Erdos137.P_le_4_pow                          -- P k ≤ 4^k (primorial; standard 3)
#print axioms Erdos137.div_le_factorization_F             -- ⌊k/p⌋ ≤ v_p(F k n) (standard 3)
#print axioms Erdos137.L_dvd_F                             -- L k ∣ F k n (Legendre; standard 3)
#print axioms Erdos137.smooth_refinement                   -- rad(F)²·L ≤ F·P² (standard 3)
#print axioms Erdos137.master_ineq                         -- n^k·L³ ≤ (k^{2k})³·P^6 (BlockRadLB)
#print axioms Erdos137.not_powerful_of_large'             -- HEADLINE': BlockRadLB → (k^{2k})³·P^6 < n^k·L³ → ¬powerful
#print axioms Erdos137.not_powerful_finite'               -- per-k finiteness (smooth-refined route)

-- Tao "very bad interval" elementary structure (this file): unconditional, no radical/abc input.
#print axioms Erdos137.prime_dvd_two_terms_eq             -- prime ≥ k divides ≤ 1 block factor (standard 3)
#print axioms Erdos137.veryBad_large_prime_sq             -- very bad + large prime ⟹ p² ∣ factor (standard 3)
#print axioms Erdos137.prime_term_gt_length_not_powerful  -- prime factor > length ⟹ not powerful (standard 3)
#print axioms Erdos137.prime_in_block_not_powerful        -- restatement (standard 3)
