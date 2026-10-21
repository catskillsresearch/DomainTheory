/-ai
The projection of an element y equals the supremum of the set of elements x such that the injection of x lies below y.

The projection of y lies below that supremum because it belongs to the set, by the inequality that the injection of the projection of y lies below y. The supremum lies below the projection of y because every member does, by the Galois connection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_proj_apply_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.lowerSet_bounded

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25, first extremal formula.** `h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`.

`h(y)` is the *greatest* member of the set (`g(h(y)) ⊑ y`, so `h(y)` is in it; every member is
`⊑ h(y)` by the Galois connection), hence it is the least upper bound. -/
theorem proj_eq_sSup (P : ProjectionPair D E) (y : E.Element) :
    P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y) := by
  apply le_antisymm
  · exact D.le_sSup _ (P.lowerSet_bounded y) (P.inj_proj_apply_le y)
  · exact D.sSup_le _ (P.lowerSet_bounded y) fun x hx => (P.galois x y).mp hx

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
