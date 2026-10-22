/-ai
The set presented by a list of endpoint pairs is the union, over the pairs on the list, of the corresponding half-open rational intervals.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- The set presented by a list of interval endpoint-pairs: the union `⋃ (r,s) ∈ L, [r,s)`. -/
def presentedIntervals (L : List (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ L, Set.Ico p.1 p.2

end DomainTheory.NeighbourhoodSystems
