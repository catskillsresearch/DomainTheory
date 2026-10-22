module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.dfaToNFA_eval

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- Choice-free version of `DFA.toNFA_correct`. -/
theorem dfaToNFA_accepts {σ : Type} (M : DFA Bool σ) : M.toNFA.accepts = M.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSe⟩
    rw [dfaToNFA_eval, Set.mem_singleton_iff] at hSe
    rw [DFA.mem_accepts, ← hSe]
    exact hS
  · intro hx
    rw [DFA.mem_accepts] at hx
    exact ⟨M.eval x, hx, by rw [dfaToNFA_eval]; exact Set.mem_singleton _⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
