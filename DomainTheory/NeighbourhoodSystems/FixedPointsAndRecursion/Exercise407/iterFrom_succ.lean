/-ai
The iterate of f from a at a successor index equals the elementwise action of f on the preceding iterate.

Unfolding the definition, the successor iterate of a function is that function after the preceding iterate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterFrom_succ (f : ApproximableMap V V) (a : V.Element) (n : ℕ) :
    f.iterFrom a (n + 1) = f.toElementMap (f.iterFrom a n) := by
  rw [iterFrom, iterFrom, Function.iterate_succ', Function.comp_apply]

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
