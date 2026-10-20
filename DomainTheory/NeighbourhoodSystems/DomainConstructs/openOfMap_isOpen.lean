module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `openOfMap f` is open: it is a union of basic opens `[X]`. -/
theorem openOfMap_isOpen (f : ApproximableMap V sierpinski) : IsOpen (openOfMap V f) := by
  intro x hx
  obtain ⟨X, hxX, hf⟩ := hx
  exact ⟨X, hxX, fun z hz => ⟨X, hz, hf⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
