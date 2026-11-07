module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.relSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
open NeighborhoodSystem ApproximableMap

theorem example_410 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      {x : V.Element},
      x ≤ f.fixElement → f.toElementMap x = x → x = f.fixElement) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      (ha : f.toElementMap f.fixElement = f.fixElement)
      (g : (relSystem f.fixElement).Element),
      (relMap f ha).toElementMap g = g →
        g = restrict f.fixElement f.fixElement (le_refl _)) :=
  ⟨@fixElement_below_unique, @relMap_unique_fixed⟩

end DomainTheory.NeighbourhoodSystems.ApproximableMap
