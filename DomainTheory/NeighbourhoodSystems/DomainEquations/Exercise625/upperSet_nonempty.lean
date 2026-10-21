/-ai
The upper set of an element x is nonempty.

The injection of x belongs to it, because the projection of that injection equals x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.proj_inj_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — "check that the set on the right is non-empty".** `g(x)` itself lies in
`{y ∣ x ⊑ h(y)}`, since `x ⊑ h(g(x)) = x`. -/
theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
