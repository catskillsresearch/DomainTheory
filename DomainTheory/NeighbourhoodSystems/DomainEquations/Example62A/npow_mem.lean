module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

@[simp] theorem npow_mem {V : NeighborhoodSystem β} {W : Set (Fin n × β)} {hn : 0 < n} :
    (npow V n hn).mem W ↔ ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X := Iff.rfl

end Example62A

end DomainTheory.NeighbourhoodSystems
