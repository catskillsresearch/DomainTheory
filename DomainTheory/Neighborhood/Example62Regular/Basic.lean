/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.MyhillNerode

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — eventually-periodic trees and regular events

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI,
*Introduction to domain equations*. After exhibiting the generalised domain equation `A ≅ Aⁿ + Aⁿ`
(formalised in `Example62A.lean`), Scott closes Example 6.2 with a *casual aside* connecting his
infinite `±`-labelled `n`-ary trees to automata theory:

> "We say that a (total) tree `a` is *eventually periodic* iff the set `{aσ ∣ σ ∈ Σ*}` is finite.
> The result is that the 'language' `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` corresponding to an eventually
> periodic tree is always a *regular event* of automata theory, and every such language has this form.
> In fact, `a` just represents the initial state of an automaton, and `aσ` represents the state after
> 'reading' a tape `σ`."

This file makes that remark precise and *proves* it. Scott's total trees over `Σ = {0, …, n-1}` are
exactly the functions `a : Σ* → Bool` assigning a `±` label (`pos`) to every node, addressed by a
finite selector `σ ∈ Σ*`. The **subtree** operation `σ ↦ aσ` is Scott's selector recursion
`aΛ = a`, `a(iσ) = (aᵢ)σ`; its *language* `L_a` is the set of selectors landing on a `+` node.

The two halves of Scott's claim are exactly the two halves of the **Myhill–Nerode theorem**: a tree
is eventually periodic (finitely many distinct subtrees) iff its language has finitely many *left
quotients* iff (Myhill–Nerode, `Language.isRegular_iff_finite_range_leftQuotient`) the language is
regular. The bridge is that the subtree `aσ` *is* the left quotient `σ⁻¹ L_a`: reading the tape `σ`
moves the automaton to the residual language, which is precisely the subtree at `σ`.

This is a `Prop`-level result (about regularity), so `Classical.choice` is unobjectionable here; the
content is entirely the combinatorics-on-words / automata correspondence, orthogonal to the
neighbourhood-system machinery.
-/

namespace DomainTheory.Neighborhood

namespace Example62Regular

open Language

variable {n : ℕ}

/-- A **total tree** over the alphabet `Σ = Fin n` (Scott's `n`-ary `±` tree): an assignment of a
`±` label (`Bool`, `true = +`) to every node, addressed by a finite selector `σ ∈ Σ*`. A tree is
*total* in Scott's sense (every node carries a genuine label), as opposed to the partial elements of
the domain `A` of `Example62A.lean` where labels may be `⊥`. -/
abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool

/-- Scott's `pos : A → T`: the `±` label at the **root** of the tree (`pos(±⟨…⟩) = true/false`). -/
def pos (a : Tree n) : Bool := a []

/-- Scott's subtree selector `σ ↦ aσ`: the subtree of `a` reached by the selector `σ`. Defined so
that `(aσ)τ = a(στ)`; the `pos`-label at node `τ` of `aσ` is the label at node `στ` of `a`. -/
def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl

/-- The `i`-th immediate subtree `aᵢ = a i` (Scott's children of the root node). -/
def child (a : Tree n) (i : Fin n) : Tree n := select a [i]

@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp

@[simp] theorem pos_select (a : Tree n) (σ : List (Fin n)) : pos (select a σ) = a σ := by
  simp [pos]

/-- **Scott's language of a tree.** `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` — the selectors that land on a
`+` node. Equivalently (by `pos_select`) the set of `σ` with `a σ = true`. A `Language (Fin n)` is
just a set of words over the alphabet, exactly Scott's "language". -/
def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}

@[simp] theorem mem_treeLang {a : Tree n} {σ : List (Fin n)} : σ ∈ treeLang a ↔ a σ = true := Iff.rfl

/-- **Eventual periodicity (Scott).** A tree `a` is *eventually periodic* iff the set of its subtrees
`{aσ ∣ σ ∈ Σ*}` is finite. (Equivalently — by the picture — the tree is built from finitely many
distinct subtrees, so it is "ultimately periodic" along every branch.) -/
def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite
end Example62Regular
end DomainTheory.Neighborhood
