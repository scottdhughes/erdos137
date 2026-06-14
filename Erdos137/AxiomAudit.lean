import Erdos137.Finiteness

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
