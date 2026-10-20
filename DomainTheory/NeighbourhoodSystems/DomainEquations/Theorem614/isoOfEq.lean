module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- The identity isomorphism induced by an object equality in any category. -/
def isoOfEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨(𝟙 X), (𝟙 X), CategoryTheory.Category.id_comp _, CategoryTheory.Category.id_comp _⟩

end Theorem614

end DomainTheory.NeighbourhoodSystems
