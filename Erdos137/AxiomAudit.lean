import Erdos137.Finiteness
import Erdos137.Base
import Erdos137.BlockFramework
import Erdos137.JointFiniteness
import Erdos137.SmoothRefinement
import Erdos137.TaoPoint
import Erdos137.SpliceFiniteness
import Erdos137.QuarticCrude
import Erdos137.SexticCrude

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

-- Triple-tiling route (JointFiniteness):
#print axioms Erdos137.rad_triples_decomp                  -- radical-of-product decomposition (proved)
#print axioms Erdos137.rad_triples_le                      -- decomposition inequality (proved)
#print axioms Erdos137.overlap_le                          -- overlap ≤ ⌊k/p⌋+1 (combinatorial core)
#print axioms Erdos137.W_dvd_factorial                     -- W ∣ k! (Legendre)
#print axioms Erdos137.W_le_pow                            -- overlap bound W ≤ k^k (proved)
#print axioms Erdos137.pow_le_F                            -- n^k ≤ F k n (proved)
#print axioms Erdos137.not_powerful_of_large              -- BlockRadLB → n>k^6 → ¬powerful (crude route)
#print axioms Erdos137.not_powerful_finite                -- per-k finiteness (crude route)

-- Smooth-part radical refinement (Base + SmoothRefinement): sharpened threshold.
#print axioms Erdos137.P_le_4_pow                          -- P k ≤ 4^k (primorial; standard 3)
#print axioms Erdos137.div_le_factorization_F             -- ⌊k/p⌋ ≤ v_p(F k n) (standard 3)
#print axioms Erdos137.L_dvd_F                             -- L k ∣ F k n (Legendre; standard 3)
#print axioms Erdos137.smooth_refinement                   -- rad(F)²·L ≤ F·P² (standard 3)
#print axioms Erdos137.master_ineq                         -- n^k·L³ ≤ (k^{2k})³·P^6 (BlockRadLB)
#print axioms Erdos137.not_powerful_of_large'             -- HEADLINE': BlockRadLB → (k^{2k})³·P^6 < n^k·L³ → ¬powerful
#print axioms Erdos137.not_powerful_finite'               -- per-k finiteness (smooth-refined route)

-- Tao "very bad interval" elementary structure (TaoPoint): unconditional, no radical/abc input.
#print axioms Erdos137.prime_dvd_two_terms_eq             -- prime ≥ k divides ≤ 1 block factor (standard 3)
#print axioms Erdos137.veryBad_large_prime_sq             -- very bad + large prime ⟹ p² ∣ factor (standard 3)
#print axioms Erdos137.prime_term_gt_length_not_powerful  -- prime factor > length ⟹ not powerful (standard 3)
#print axioms Erdos137.prime_in_block_not_powerful        -- restatement (standard 3)

-- g=5 honest finiteness + abstract splice machine (SpliceFiniteness): no global BHP.
#print axioms Erdos137.W5_le_pow                          -- overlap bound W5 ≤ k^k (proved, standard 3)
#print axioms Erdos137.master_ineq5                       -- n^{3k}·L^5 ≤ (k^{2k})^5·P^{10} (BlockRadLB5 premise)
#print axioms Erdos137.not_powerful_g5                    -- BlockRadLB5 → (k^{2k})^5·P^{10} < n^{3k}·L^5 → ¬powerful
#print axioms Erdos137.upper_half_prime_not_powerful      -- n≤k → ¬powerful (UNCONDITIONAL, Bertrand; standard 3)
#print axioms Erdos137.powerful_bound_g5                  -- BlockRadLB5 → powerful → n ≤ Msplice k (standard 3)
#print axioms Erdos137.g5_finiteness                      -- BlockRadLB5 → {n | powerful (F k n)} finite (honest, no BHP)
#print axioms Erdos137.prime_range_not_powerful           -- PrimeInBlockOnRange Range → Range k n → ¬powerful (premise)
#print axioms Erdos137.abstract_splice_no_counterexamples -- CoversAll + ranged prime + high input → ¬powerful (premises)

-- Parametric g-block framework (BlockFramework.lean): unifies g=3 and g=5.
#print axioms Erdos137.Wg_le_pow                          -- overlap bound Wg ≤ k^k (proved, standard 3)
#print axioms Erdos137.Wg_dvd_factorial                   -- Wg ∣ k! (Legendre; standard 3)
#print axioms Erdos137.master_ineq_g                      -- n^{(g-2)k}·L^g ≤ (k^{2k})^g·P^{2g} (BlockRadLBg premise)
#print axioms Erdos137.not_powerful_g                     -- BlockRadLBg → Mg < n^{(g-2)k}·L^g → ¬powerful (standard 3)
#print axioms Erdos137.powerful_bound_g                   -- BlockRadLBg → powerful → n ≤ Mg g k (standard 3)
#print axioms Erdos137.g_finiteness                       -- BlockRadLBg → {n | powerful (F k n)} finite (generic g)

-- Crude (non-smooth) route + g=4 (BlockFramework / QuarticCrude): explicit integer threshold k^{2g/(g-2)}.
#print axioms Erdos137.master_ineq_crude_g                -- BlockRadLBg → n^{g-2} ≤ k^{2g} (crude, standard 3)
#print axioms Erdos137.not_powerful_crude_g               -- BlockRadLBg → k^{2g} < n^{g-2} → ¬powerful (standard 3)
#print axioms Erdos137.crude_g_finiteness                 -- BlockRadLBg → {n | powerful (F k n)} finite (crude, generic g)
#print axioms Erdos137.not_powerful_of_large_g4           -- BlockRadLB4 → k^4 < n → ¬powerful (sharp quartic, standard 3)
#print axioms Erdos137.g4_crude_finiteness                -- BlockRadLB4 → {n | powerful (F k n)} finite (g=4, standard 3)
#print axioms Erdos137.not_powerful_of_large_g6           -- BlockRadLB6 → k^3 < n → ¬powerful (sharp sextic, standard 3)
#print axioms Erdos137.g6_crude_finiteness                -- BlockRadLB6 → {n | powerful (F k n)} finite (g=6, standard 3)
