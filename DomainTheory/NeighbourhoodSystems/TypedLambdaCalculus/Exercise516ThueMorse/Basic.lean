/-ai
This file gathers and re-exports the domain of Exercise 5.16, the binary-digit library, the Thue–Morse substitution with its empty and cons clauses, the operator sending x to 0 consed onto the merge of the negation of x with the tail of x, the parity bit function with its zero clause, the prefixes with their zero clause, and the least fixed point t of that operator, as the setting for the digit characterization of t.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tElt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_zero

@[expose] public section

/-!
# Exercise 5.16 follow-up (Scott 1981, PRG-19, Lecture V) — the Thue–Morse sequence `t`

The unfinished tail of Exercise 5.16. Returning to the domain `C` of finite/infinite binary
sequences (Example 4.4), Scott studies the element

`t = 0·merge(neg t, tail t)`,

the least fixed point of `Φ(x) = 0·merge(neg x, tail x)`, and (Lambek's observation) identifies its
`n`-th digit with the parity of the binary digits of `n` — the **Thue–Morse sequence**.

This module formalizes:

* **Step 0 — the element and its unfolding.** `tElt := Φ.fixElement` and `tElt_unfold` proving
  `t = 0·merge(neg t, tail t)`.
* **The Thue–Morse morphism `expand`** (the substitution `0 ↦ 01`, `1 ↦ 10`) and the key bridge
  `Phi_strBot_expand`: applied to a partial element `(0σ)⊥`, the operator `Φ` is exactly `expand`.
  Consequently the finite approximants of the least fixed point are `Φⁿ⁺¹(⊥) = (expandⁿ[0])⊥`
  (`iterElem_succ_eq`).
* **The parity bit-function `tm`** with `tm n = ⊕ (binary digits of n)` (via `Nat.bits`), its
  recurrences `tm (2n) = tm n`, `tm (2n+1) = ¬ tm n`, and the bridge `expand_iterate_eq` showing the
  approximant strings are precisely the Thue–Morse parity prefixes `tmList (2ⁿ)`.
* **Property (a) — the digit characterization.** `tElt_mem_cone_iff`: a finite string `σ` is a prefix
  of `t` **iff** `σ` is the length-`σ.length` Thue–Morse prefix (`σ = tmList σ.length`); and the
  digit reading `tElt_digit : (tmList n ++ [tm n])⊥ ≤ t`, i.e. the `n`-th digit of `t` is `tm n`,
  the parity of the binary digits of `n` (Lambek).

The `tElt` *data* is choice-free; the `Prop`-level digit facts may use `Classical.choice` (through the
project's `eq_of_toElementMap_principal` and the truth-domain primitives), exactly like the existing
uniqueness lemmas. Overlap-freeness (property (b)) is a self-contained word-combinatorics theorem and
lives in its own module.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-! ### The Thue–Morse morphism `expand` (`0 ↦ 01`, `1 ↦ 10`). -/




/-! ### `Φ` on a partial element computes by interleaving — and equals `expand`. -/


/-! ### The finite approximants of the least fixed point are the morphism iterates. -/

/-! ### The parity bit-function `tm` and its prefixes. -/





/-! ### Step 0 — the element `t` and its unfolding. -/


/-! ### Property (a) — the digit characterization. -/
end DomainTheory.NeighbourhoodSystems.Exercise516
