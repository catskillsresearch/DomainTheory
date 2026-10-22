/-ai
The empty list of endpoint pairs presents the empty set.

Extensionality and simplification of the empty union give the identity.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.mem_presentedIntervals

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem presentedIntervals_nil : presentedIntervals ([] : List (ℚ × ℚ)) = ∅ := by
  ext x; simp

end DomainTheory.NeighbourhoodSystems
