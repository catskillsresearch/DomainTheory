module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.ProjectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

end Subsystem

end DomainTheory.NeighbourhoodSystems
