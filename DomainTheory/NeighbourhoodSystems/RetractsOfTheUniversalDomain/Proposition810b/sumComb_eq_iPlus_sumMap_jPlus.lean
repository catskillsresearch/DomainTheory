/-ai
The sum combination of two approximable self-maps equals the plus injection composed with their sum map composed with the plus projection.

Extensionality of approximable maps reduces the equality to the action on an element, and composition of element maps unfolds both sides. The image under the plus projection reaches the left copy, the right copy, or neither. On the left, the left formulas for the sum combination and the sum map agree. On the right, the right formulas agree. On neither, the neither formula for the sum combination, the characterization of neither as bottom, the fact that the sum map sends bottom to bottom, and the fact that the plus injection sends the bottom of the sum to the bottom of the universal domain agree; the last step uses that the plus injection composed with the plus projection lies below the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_bot_eq_bot_of_comp_le_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.reaches_neither_iff_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_right

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_neither
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_of_right
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section SumCase

variable (a b : ApproximableMap U U)

/-- **`sumComb a b = i₊ ∘ (a+b) ∘ j₊`, at the level of approximable maps**, where `a+b` on the
right is Exercise 3.19's `sumMap`. Proved by case-splitting on `sum_element_trichotomy` of
`jPlus.toElementMap x`, matching `sumMap`'s elementwise formulas
(`toElementMap_sumMap_of_left/right`, `sumMap_bot`) against `sumComb`'s own
(`toElementMap_sumComb_of_left/right/neither`, `Proposition810.lean`). The bottom case additionally
needs `iPlus.toElementMap (sum U U ..).bot = U.bot`, from `iPlus_comp_jPlus_le`. -/
theorem sumComb_eq_iPlus_sumMap_jPlus :
    sumComb a b = iPlus.comp
      ((sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty) (h₀' := U_mem_nonempty)
          (h₁' := U_mem_nonempty) a b).comp jPlus) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL, toElementMap_sumMap_of_left hL]
  · rw [toElementMap_sumComb_of_right hR, toElementMap_sumMap_of_right hR]
  · rw [toElementMap_sumComb_of_neither hN, reaches_neither_iff_eq_bot.mp hN, sumMap_bot,
      toElementMap_bot_eq_bot_of_comp_le_idMap iPlus_comp_jPlus_le]

end SumCase

end DomainTheory.NeighbourhoodSystems
