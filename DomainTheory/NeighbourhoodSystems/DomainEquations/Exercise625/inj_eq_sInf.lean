/-ai
The injection of an element x equals the infimum of the set of elements y such that x lies below the projection of y.

The injection of x lies below that infimum because the Galois connection places it below every member of the set. The infimum lies below the injection of x because that image belongs to the set, by the identity that the projection of the injection of x equals x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.proj_inj_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.upperSet_nonempty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair







/-- **Exercise 6.25, second extremal formula.** `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`.

`g(x)` is the *least* member of the set (`x ⊑ h(g(x)) = x`, so `g(x)` is in it; every member is
`⊒ g(x)` by the Galois connection), hence it is the greatest lower bound. -/
theorem inj_eq_sInf (P : ProjectionPair D E) (x : D.Element) :
    P.inj.toElementMap x = E.sInf (P.upperSet x) (P.upperSet_nonempty x) := by
  apply le_antisymm
  · exact E.le_sInf _ (P.upperSet_nonempty x) _ fun y hy => (P.galois x y).mpr hy
  · refine E.sInf_le _ (P.upperSet_nonempty x) ?_
    rw [mem_upperSet, P.proj_inj_apply x]

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
