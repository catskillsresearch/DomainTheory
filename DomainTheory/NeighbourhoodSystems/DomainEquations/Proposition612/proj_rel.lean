module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.ProjectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

end Subsystem

end DomainTheory.NeighbourhoodSystems
