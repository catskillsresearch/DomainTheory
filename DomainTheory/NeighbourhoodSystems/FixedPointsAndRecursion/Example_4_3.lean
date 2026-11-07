module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Scott's Example 4.3: the structured number domain with succ, pred, and zero. -/
theorem example_43 :
    (∀ n : ℕ, succMap.toElementMap (natElem n) = natElem (n + 1)) ∧
    (∀ k : ℕ, predMap.toElementMap (natElem (k + 1)) = natElem k) ∧
    (predMap.toElementMap (natElem 0) = N.bot) ∧
    (succMap.toElementMap N.bot = N.bot) ∧
    (predMap.toElementMap N.bot = N.bot) ∧
    (zeroMap.toElementMap (natElem 0) = Example23.trueElt) ∧
    (∀ n : ℕ, zeroMap.toElementMap (natElem (n + 1)) = Example23.falseElt) ∧
    (zeroMap.toElementMap N.bot = T.bot) ∧
    (∀ n : ℕ, predMap.toElementMap (succMap.toElementMap (natElem n)) = natElem n) :=
  ⟨@succMap_natElem, @predMap_natElem_succ, predMap_natElem_zero,
   succMap_bot, predMap_bot, zeroMap_natElem_zero, @zeroMap_natElem_succ, zeroMap_bot,
   @predMap_succMap_natElem⟩

end DomainTheory.NeighbourhoodSystems.Example43
