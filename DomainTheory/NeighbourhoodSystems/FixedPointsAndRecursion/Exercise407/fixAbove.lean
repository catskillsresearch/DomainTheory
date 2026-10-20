module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The fixed point of `f` lying above a pre-fixed-point candidate `a` (with `a ⊑ f(a)`),
constructed as the directed union `⊔ₙ fⁿ(a)`. -/
def fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) : V.Element :=
  NeighborhoodSystem.iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
