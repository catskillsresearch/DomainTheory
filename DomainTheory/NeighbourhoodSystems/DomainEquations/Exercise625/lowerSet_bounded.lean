/-ai
The lower set of an element y is bounded.

The projection of y is an upper bound, because the Galois connection turns the defining inequality into membership below that projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair




/-- The set `{x ∣ g(x) ⊑ y}` is bounded: `h(y)` is an upper bound (it is in fact the top). -/
theorem lowerSet_bounded (P : ProjectionPair D E) (y : E.Element) :
    D.Bounded (P.lowerSet y) :=
  ⟨P.proj.toElementMap y, fun _ hx => (P.galois _ y).mp hx⟩

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
