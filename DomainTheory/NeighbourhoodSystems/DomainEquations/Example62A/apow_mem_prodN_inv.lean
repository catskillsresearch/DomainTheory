/-ai
If the proper product of a family X is a neighbourhood of the n-fold power of A, then every component of X belongs to MemA.

Unpack the product witness and the equality of products, then rewrite each component by injectivity of prodN.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Apow

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem apow_mem_prodN_inv (hn : 0 < n) {X : Fin n → Set Str} (h : (Apow hn).mem (prodN X)) :
    ∀ j, MemA n (X j) := by
  obtain ⟨X', hX', heq⟩ := h
  intro j; rw [prodN_injective heq j]; exact hX' j

end Example62A

end DomainTheory.NeighbourhoodSystems
