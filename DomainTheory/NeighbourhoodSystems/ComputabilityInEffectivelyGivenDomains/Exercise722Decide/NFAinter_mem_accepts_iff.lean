module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter_mem_eval_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

section NFAinterLemmas

variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

theorem NFAinter_mem_accepts_iff (x : List Bool) :
    x ∈ (NFAinter M₁ M₂).accepts ↔ x ∈ M₁.accepts ∧ x ∈ M₂.accepts := by
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [NFAinter_mem_eval_iff] at hpe
    exact ⟨⟨p.1, hp.1, hpe.1⟩, ⟨p.2, hp.2, hpe.2⟩⟩
  · rintro ⟨⟨s, hs, hse⟩, ⟨t, ht, hte⟩⟩
    exact ⟨(s, t), ⟨hs, ht⟩, (NFAinter_mem_eval_iff M₁ M₂ x (s, t)).mpr ⟨hse, hte⟩⟩

end NFAinterLemmas

end Exercise722

end DomainTheory.NeighbourhoodSystems
