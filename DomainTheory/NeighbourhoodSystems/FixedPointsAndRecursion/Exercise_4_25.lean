module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.unarySeq

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap NatDom DomainTheory.NeighbourhoodSystems.UnarySeq

theorem example_425 :
    relateNToC1.toElementMap NatDom.N.bot = C1.bot ∧
    (∀ n : ℕ, relateNToC1.toElementMap (NatDom.natElem n) = oneElem n) ∧
    consMap.toElementMap infElt = infElt ∧
    (∀ n : ℕ, consMap.toElementMap (oneBot n) = oneBot (n + 1)) ∧
    (∀ n : ℕ, consMap.toElementMap (oneElem n) = oneElem (n + 1)) :=
  ⟨relateNToC1_bot, relateNToC1_natElem, infElt_eq, consMap_oneBot, consMap_oneElem⟩

