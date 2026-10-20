/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits

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

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b (¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl

/-! ### `Φ` on a partial element computes by interleaving — and equals `expand`. -/

/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))

/-! ### The finite approximants of the least fixed point are the morphism iterates. -/

/-! ### The parity bit-function `tm` and its prefixes. -/

/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false

@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]

/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm

@[simp] theorem tmList_zero : tmList 0 = [] := rfl

/-! ### Step 0 — the element `t` and its unfolding. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t = 0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement

/-! ### Property (a) — the digit characterization. -/
end DomainTheory.NeighbourhoodSystems.Exercise516
