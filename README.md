# Erdős Problem #137: powerful products of consecutive integers (conditional finiteness)

A short Lean 4 / Mathlib formalization for Erdős Problem #137 (see erdosproblems.com/137).

Erdős Problem #137 (Erdős-Selfridge) asks whether the product of `k ≥ 3` consecutive
positive integers `F(k,n) = n(n+1)...(n+k-1)` can ever be **powerful** (a number `N`
with `p ∣ N ⟹ p² ∣ N`). It is open.

## What is formalized

Under the **Granville-Langevin radical lower bound** `RadLB k` (for squarefree
`g ∈ ℤ[x]`, the abc conjecture gives `rad(g(n)) ≫ n^{deg g - 1 - ε}`, hence
`rad(F(k,n)) ≫ n^{k-1-ε}`), the product `F(k,n)` is powerful for only finitely many `n`,
for each fixed `k ≥ 3`. `RadLB` is taken as an **explicit hypothesis**; the abc-conditional
radical bound itself is *not* formalized here.

| Theorem | Statement |
|---|---|
| `lemma_star` | unconditional: `rad m ^ 2 * B2 m ≤ m ^ 2` |
| `powerful_rad_sq_le` | a powerful `N ≠ 0` satisfies `rad N ^ 2 ≤ N` |
| `erdos137_eventually_not_powerful` | `k ≥ 3`, `RadLB k` ⟹ `F k n` is not powerful for all large `n` |
| `erdos137_finite` | `k ≥ 3`, `RadLB k` ⟹ `{n ≥ 1 : F k n is powerful}` is finite |

All with zero `sorry`, no `native_decide`, and standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).

## Attribution

This is a formalization of a **known** result, not a new theorem. Under abc, the
finiteness follows from the Granville-Langevin radical lower bound (Langevin; and
A. Granville, [*ABC allows us to count squarefrees*](https://doi.org/10.1155/S1073792898000592),
IMRN 1998, no. 19, 991-1009). It is discussed by T. N. Shorey and R. Tijdeman,
[*Arithmetic properties of blocks of consecutive integers*](https://arxiv.org/abs/1612.05438)
(Springer, 2016), §8.1, which records `rad(F(k,n)) ≫_k n^{k-1-ε}` under abc, with sharper
power-free-part bounds due to B. M. M. de Weger and C. E. van de Woestijne,
[*On the power-free parts of consecutive integers*](https://doi.org/10.4064/aa-90-4-387-395),
Acta Arith. 90 (1999), 387-395. (For `k = 2` the product is powerful infinitely often.)

## Verifying

```sh
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.28.0`, Mathlib pinned in `lake-manifest.json`. The build
prints an axiom report (`Erdos137/AxiomAudit.lean`).

## License

Apache-2.0.
