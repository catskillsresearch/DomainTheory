/-ai
If a lies below f(a), then a lies below the directed union of the iterates of f from a.

The zero-th iterate lies below that directed union, and the zero law says that this iterate is a.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `a ⊑ fixAbove f ha`: the constructed fixed point lies above `a` (it is the `n = 0` term). -/
theorem le_fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    a ≤ f.fixAbove ha := by
  have := NeighborhoodSystem.le_iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩) 0
  rwa [iterFrom_zero] at this

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
