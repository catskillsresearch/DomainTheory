/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Continuous

@[expose] public section

/-!
# Scott 1976, §1 — graphs of continuous functions

`graph` / `fun` (Table 2 application) and Theorem 1.2.
-/

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1, Definition.**
`graph(f) = {(n, m) | m ∈ f(e n)}`. -/
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

/-- **Scott 1976, §1, Definition / Table 2.**
`fun(u)(x) = {m | ∃ e n ⊆ x. (n, m) ∈ u}`. -/
def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

infixl:70 " ⬝ " => funOf

/-- **Scott 1976, Theorem 1.2 (iii).** Equality in (ii) iff `u` is downward
closed in the finite-set argument: `(k, m) ∈ u` and `e k ⊆ e n` imply `(n, m) ∈ u`. -/
def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

/-- Abstraction: `λ x. τ` as a graph (Table 2). -/
def lam (τ : Pomega → Pomega) : Pomega := graph τ
end DomainTheory.DataTypesAsLattices
