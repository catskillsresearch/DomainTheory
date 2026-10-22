module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
end DomainTheory.NeighbourhoodSystems
