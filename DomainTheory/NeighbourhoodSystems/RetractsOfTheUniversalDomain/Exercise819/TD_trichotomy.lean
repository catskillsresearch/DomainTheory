/-ai
Every element of the truth-value domain is the bottom element, the true element, or the false element.

This is the three-way classification of elements of the neighbourhood system of Example 1.2, read with the names of Example 2.3.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u





/-- **`T`'s elements, named via `Example23`.** The three-way classification of `Example12`,
restated with `Example23`'s `⊥`/`true`/`false` names (they are the *same* terms by `rfl`). -/
theorem TD_trichotomy (t : TD.Element) :
    t = Example23.botElt ∨ t = Example23.trueElt ∨ t = Example23.falseElt :=
  Example12.neighborhoodSystem.element_classification t

end DomainTheory.NeighbourhoodSystems
