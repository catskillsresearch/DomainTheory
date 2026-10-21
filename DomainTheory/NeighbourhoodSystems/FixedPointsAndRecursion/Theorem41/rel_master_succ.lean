/-ai
If the n-th iterate of an approximable endomap relates the master neighbourhood to a set, then the successor iterate does as well.

Commutation rewrites the successor iterate as the n-th iterate composed on the right with the map. The map relates the master neighbourhood to itself, and the hypothesis is the remaining step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iter_comm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Scott's "a sequence for an `X ∈ x` can always be extended": if `Δ fⁿ X`, then `Δ f^{n+1} X`
(prepend a `Δ`-step, using `Δ f Δ`). -/
theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
