import Erdos137.Finiteness
import Erdos137.JointFiniteness

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
#print axioms Erdos137.not_powerful_of_large              -- HEADLINE: BlockRadLB → n>k^6 → ¬powerful
#print axioms Erdos137.not_powerful_finite                -- per-k finiteness
