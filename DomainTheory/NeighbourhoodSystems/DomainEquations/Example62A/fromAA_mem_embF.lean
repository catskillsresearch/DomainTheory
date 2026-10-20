module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

@[simp] theorem fromAA_mem_embF (hn : 0 < n) {s : (AAsys hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (fromAA hn s).mem (embTuple false X) ↔ s.mem (inj₀ (prodN X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ X)
    · rw [funext (embTuple_injective heq)]; exact hs
    · exact absurd heq
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX ⟨0, hn⟩)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
