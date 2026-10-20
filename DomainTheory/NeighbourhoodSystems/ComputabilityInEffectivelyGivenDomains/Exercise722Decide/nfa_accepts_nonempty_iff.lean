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

/-- A nonempty accepted language ⟺ some accept state is reachable by reading some word. -/
theorem nfa_accepts_nonempty_iff (M : NFA Bool σ) :
    M.accepts.Nonempty ↔ ∃ s ∈ M.accept, ∃ x, s ∈ M.eval x := by
  constructor
  · rintro ⟨x, S, hS, hSe⟩; exact ⟨S, hS, x, hSe⟩
  · rintro ⟨S, hS, x, hSe⟩; exact ⟨x, S, hS, hSe⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
