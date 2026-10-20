module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f` commutes with its own iterate: `f ∘ fⁿ = fⁿ ∘ f`. Proved by induction using associativity
and the identity laws. -/
theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
