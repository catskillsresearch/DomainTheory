/-ai
The set of elements sent to the top by an approximable map into the Sierpiński domain is an open set of elements.

If an element lies in the set, some neighbourhood of it is related to the empty set, and every element of that neighbourhood lies in the set by the same relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `openOfMap f` is open: it is a union of basic opens `[X]`. -/
theorem openOfMap_isOpen (f : ApproximableMap V sierpinski) : IsOpen (openOfMap V f) := by
  constructor
  intro x hx
  obtain ⟨X, hxX, hf⟩ := hx
  exact ⟨X, hxX, fun z hz => ⟨X, hz, hf⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
