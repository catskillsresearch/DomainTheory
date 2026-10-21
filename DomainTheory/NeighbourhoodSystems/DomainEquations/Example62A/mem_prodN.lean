/-ai
A pair lies in the proper product of a family X if and only if its second component lies in the set indexed by its first component.

The equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

@[simp] theorem mem_prodN {X : Fin n → Set β} {p : Fin n × β} : p ∈ prodN X ↔ p.2 ∈ X p.1 := Iff.rfl

end Example62A

end DomainTheory.NeighbourhoodSystems
