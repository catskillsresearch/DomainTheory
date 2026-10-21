/-ai
Any two members of the lower set of an element y have a common upper bound that still lies in the set.

The projection of y lies in the set because the injection of that projection lies below y, and both members lie below the projection by the Galois connection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_proj_apply_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair




/-- **Exercise 6.25 — "check that the set on the right is directed".** Any two members of
`{x ∣ g(x) ⊑ y}` have a common upper bound *inside the set*, namely `h(y)` itself (the down-set of
`h(y)` has `h(y)` as a top, so it is trivially directed). -/
theorem lowerSet_directed (P : ProjectionPair D E) (y : E.Element) :
    ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y,
      ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c := by
  intro a ha b hb
  exact ⟨P.proj.toElementMap y, P.inj_proj_apply_le y,
    (P.galois a y).mp ha, (P.galois b y).mp hb⟩

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
