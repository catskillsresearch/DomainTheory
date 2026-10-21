/-ai
The map from the flat naturals to the unary sequence system is the strict lift that sends each numeral to the total element of that length.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.oneElem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 4.25 — relating `N` and `C₁`.** The "length ↦ unary expansion" map `N → C₁` sending
the numeral `n̂` to the finite string `1ⁿ` and `⊥` to `⊥` (strict). Built from the strict-lift
combinator `constLiftN` of Example 4.3. -/
def relateNToC1 : ApproximableMap Example43.N C1 := Example43.constLiftN C1 oneElem

end DomainTheory.NeighbourhoodSystems.Exercise425
