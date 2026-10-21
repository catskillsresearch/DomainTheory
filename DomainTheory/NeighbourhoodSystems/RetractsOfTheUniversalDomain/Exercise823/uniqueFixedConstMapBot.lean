/-ai
The fixed-point set of the constant-bottom map is a singleton type. Its default element is the bottom, which is fixed because the constant map sends the bottom to the bottom, and every fixed point equals the bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.eq_bot_of_fixed_constMap_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}

instance uniqueFixedConstMapBot :
    Unique {y : E.Element // (constMap E E.bot).toElementMap y = y} where
  default := ⟨E.bot, toElementMap_constMap E.bot E.bot⟩
  uniq := fun ⟨_y, hy⟩ => Subtype.ext (eq_bot_of_fixed_constMap_bot hy)

end Exercise823

end DomainTheory.NeighbourhoodSystems
