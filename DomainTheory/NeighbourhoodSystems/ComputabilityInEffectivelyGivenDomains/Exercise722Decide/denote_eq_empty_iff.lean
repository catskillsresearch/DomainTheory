/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise722DFA
public import DomainTheory.Neighborhood.Exercise722Cat
public import DomainTheory.Neighborhood.Exercise722Words
public import DomainTheory.Neighborhood.Exercise722Decide.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}














variable {σ : Type}

/-- **Definition 7.1 relation (ii) as a reachability problem.** `denote e` is empty iff no accept
state of its `Fintype` automaton is reachable. The right-hand side ranges over the finite state set
`autState e`; the only non-finite-looking quantifier (`∀ x`) is what a reachability search eliminates. -/
theorem denote_eq_empty_iff (e : SExpr) :
    denote e = ∅ ↔ ∀ s ∈ (toNFA e).accept, ∀ x, s ∉ (toNFA e).eval x := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s hs x hse
    exact h x (by rw [← toNFA_accepts e]; exact ⟨s, hs, hse⟩)
  · intro h x hx
    rw [← toNFA_accepts e] at hx
    obtain ⟨s, hs, hse⟩ := hx
    exact h s hs x hse

end Exercise722
end DomainTheory.Neighborhood
