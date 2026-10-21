/-ai
The image of an element under the projection consists of the neighbourhoods of that element which already belong to the subdomain.

A witness in the image is a neighbourhood of the element contained in a neighbourhood of the subdomain, and upward closure returns that neighbourhood of the subdomain as a neighbourhood of the element. A neighbourhood of the subdomain that already belongs to the element is related to itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}





/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`. -/
theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
