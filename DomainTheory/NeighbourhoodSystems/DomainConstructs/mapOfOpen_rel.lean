module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mapOfOpen_rel (U : Set V.Element) (X : Set α) (Y : Set Unit) :
    (mapOfOpen V U).rel X Y ↔ V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise325
