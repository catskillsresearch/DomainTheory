/-ai
The infinite unary sequence is the least fixed point of the successor map on the unary sequence system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.consMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 4.25 — the infinite unary sequence `1^∞`.** Unlike the flat domain `N` (whose only
elements are `⊥` and the numerals `n̂`), `C₁` has a genuine *infinite* element: the least fixed point
of the successor `x ↦ 1x`, satisfying `1^∞ = 1·1^∞` (`infElt_eq`). This is what distinguishes the
*non-flat* `C₁` (the true analogue of `C`) from `N`. -/
def infElt : C1.Element := consMap.fixElement

end DomainTheory.NeighbourhoodSystems.Exercise425
