/-ai
The total element of Example 1.2 determined by the singleton of 0 does not lie below the total element determined by the singleton of 1.

The singleton of 0 belongs to the first element. If the inequality held, that singleton would belong to the second element, hence would equal the master or equal the singleton of 1, contradicting the two distinctness facts.
ai-/
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
