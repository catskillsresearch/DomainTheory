/-ai
The fixed-point set of the constant-bottom map is order-isomorphic to the terminal neighbourhood system. Both maps send every element to the default element. They are inverse because every fixed point equals the default and every element of the terminal system equals the default. The order condition holds because any two fixed points are equal and the default element is related to itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.uniqueFixedConstMapBot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}

/-- The singleton fixed-point set of the constant-bottom map is order-isomorphic to the (also
singleton) terminal system `unitSys` (`Exercise315.lean`). -/
def finitaryWitnessEquivBot (E : NeighborhoodSystem α) :
    {y : E.Element // (constMap E E.bot).toElementMap y = y} ≃o unitSys.Element where
  toFun _ := default
  invFun _ := default
  left_inv a := (Unique.eq_default a).symm
  right_inv b := (Unique.eq_default b).symm
  map_rel_iff' := by
    intro a b
    have hab : a = b := (Unique.eq_default a).trans (Unique.eq_default b).symm
    exact iff_of_true (le_refl default) (le_of_eq hab)

end Exercise823

end DomainTheory.NeighbourhoodSystems
