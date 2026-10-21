/-ai
On objects, the endofunctor sending a strict domain X to the three-way sum of the unit with two copies of X returns the strict domain whose tokens are an optional sum of a unit with two copies of the original tokens, whose neighbourhood system is the three-way separated sum of the unit system with two copies of the original system, and whose neighbourhoods are nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum3_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-- **The functor `T(X) = 𝟙 + X + X` on objects.** Over `D`, the system is the genuine three-way
separated sum `𝟙 + D + D` (Example 6.2's `sum3`, with `𝟙 = unitSys`), again `∅`-free by
`sum3_nonempty`. -/
abbrev tcObj (D : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Option (Unit ⊕ D.carrier ⊕ D.carrier)
  sys := sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty
  nonempty := sum3_nonempty

end DomainTheory.NeighbourhoodSystems
