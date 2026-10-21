/-ai
The restriction of an element x lying below a to the relativized system is the filter with the same membership as x. Membership in x implies membership in a. The master belongs to x. Intersection is inherited from x. Upward closure in the relativized system follows from upward closure of x, since a neighbourhood of a is a neighbourhood of the original system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `Dₐ`-filter obtained from an element `x ⊑ a` by restriction (same membership). -/
def restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) : (relSystem a).Element where
  mem X := x.mem X
  sub := fun h => hx _ h
  master_mem := x.master_mem
  inter_mem := fun hX hY => x.inter_mem hX hY
  up_mem := fun hX hY hXY => x.up_mem hX (a.sub hY) hXY

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
