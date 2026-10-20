module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl

end DomainTheory.NeighbourhoodSystems
