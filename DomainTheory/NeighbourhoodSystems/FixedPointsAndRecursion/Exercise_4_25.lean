module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.unarySeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Example43 Exercise425

theorem example_425 :
    relateNToC1.toElementMap Example43.N.bot = C1.bot ∧
    (∀ n : ℕ, relateNToC1.toElementMap (Example43.natElem n) = oneElem n) ∧
    consMap.toElementMap infElt = infElt ∧
    (∀ n : ℕ, consMap.toElementMap (oneBot n) = oneBot (n + 1)) ∧
    (∀ n : ℕ, consMap.toElementMap (oneElem n) = oneElem (n + 1)) :=
  ⟨relateNToC1_bot, relateNToC1_natElem, infElt_eq, consMap_oneBot, consMap_oneElem⟩

end DomainTheory.NeighbourhoodSystems
