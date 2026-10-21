/-ai
If every component of a family Y belongs to MemA, then the right injection of the proper product of Y is a neighbourhood of the separated sum Aⁿ + Aⁿ.

It is the right-summand clause, and apow_mem_prodN supplies the product membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem aa_mem_inj₁ (hn : 0 < n) {Y : Fin n → Set Str} (hY : ∀ j, MemA n (Y j)) :
    (AAsys hn).mem (inj₁ (prodN Y)) := Or.inr (Or.inr ⟨prodN Y, apow_mem_prodN hn hY, rfl⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
