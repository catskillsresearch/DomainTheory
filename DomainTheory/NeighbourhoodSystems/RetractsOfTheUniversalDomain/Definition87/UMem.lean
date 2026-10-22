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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Membership in Scott's universal family: non-empty subsets of `[0,1)` presentable as a
finite union of rational half-open intervals. -/
def UMem (X : Set ℚ) : Prop :=
  (∃ L : List (ℚ × ℚ), X = presentedIntervals L) ∧ X.Nonempty ∧ X ⊆ Set.Ico (0 : ℚ) 1

end DomainTheory.NeighbourhoodSystems
