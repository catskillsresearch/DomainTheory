module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem


/-- The two total elements are incomparable: `elemZero ⋢ elemOne`. -/
theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h Example12.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm

end DomainTheory.NeighbourhoodSystems.Exercise412
