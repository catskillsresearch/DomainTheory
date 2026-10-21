/-ai
The n-th approximant of an approximable endomap is the elementwise image of the bottom element under the n-fold iterate of the map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_fixElement

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `n`-th approximant `fⁿ(⊥)` of the least fixed point. -/
def iterElem (f : ApproximableMap V V) (n : ℕ) : V.Element := (f.iterMap n).toElementMap V.bot

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
