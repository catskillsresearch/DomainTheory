module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.elemOne_not_le_elemZero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.elemZero_not_le_elemOne
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.idMap_fixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem





/-- **Exercise 4.12 (Scott 1981, PRG-19).** `I_T` has no *greatest* (hence no maximum) fixed point:
the two total elements `elemZero`, `elemOne` are both fixed points, are incomparable, and no element
dominates both. -/
theorem no_greatest_fixedPoint :
    ¬ ∃ z : T.Element, (idMap T).toElementMap z = z ∧
      ∀ x, (idMap T).toElementMap x = x → x ≤ z := by
  rintro ⟨z, _, hz⟩
  have h0 : elemZero ≤ z := hz elemZero (idMap_fixed elemZero)
  have h1 : elemOne ≤ z := hz elemOne (idMap_fixed elemOne)
  rcases element_classification z with rfl | rfl | rfl
  · exact (bot_lt_elemZero).2 h0
  · exact elemOne_not_le_elemZero h1
  · exact elemZero_not_le_elemOne h0

end DomainTheory.NeighbourhoodSystems.Exercise412
