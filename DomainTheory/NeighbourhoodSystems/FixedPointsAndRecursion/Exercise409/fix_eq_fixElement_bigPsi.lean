module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_fix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_least

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix = fix(Ψ)`: `fix` is the least fixed point of `Ψ`,
i.e. coincides with Theorem 4.1's canonical least fixed point `fixElement Ψ`. -/
theorem fix_eq_fixElement_bigPsi (V : NeighborhoodSystem α) :
    toFilter (fixMap V) = (bigPsi V).fixElement := by
  apply le_antisymm
  · exact bigPsi_least V _ (le_of_eq (toElementMap_fixElement (bigPsi V)))
  · exact fixElement_le_of_toElementMap_le (bigPsi V) (le_of_eq (bigPsi_fix V))

end DomainTheory.NeighbourhoodSystems
