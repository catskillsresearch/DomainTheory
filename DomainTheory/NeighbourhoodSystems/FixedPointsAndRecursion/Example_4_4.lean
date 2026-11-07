module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.seqDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- Scott's Example 4.4: cons maps act by prepending on cones and total strings; alternating
fixed point of false-then-true cons. -/
theorem example_44 :
    ((consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt) ∧
    (∀ (b : Bool) (σ : Str), (consMap b).toElementMap (strBot σ) = strBot (b :: σ)) ∧
    (∀ (b : Bool) (σ : Str), (consMap b).toElementMap (strElem σ) = strElem (b :: σ)) :=
  ⟨altElt_eq, @consMap_strBot, @consMap_strElem⟩

end DomainTheory.NeighbourhoodSystems.Example44
