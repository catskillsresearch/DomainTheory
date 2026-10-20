module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
import all Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
import all Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
import all Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset
import all Mathlib.Order.CompleteLattice.Finset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_presentedIntervals {L : List (ℚ × ℚ)} {x : ℚ} :
    x ∈ presentedIntervals L ↔ ∃ p ∈ L, p.1 ≤ x ∧ x < p.2 := by
  simp only [presentedIntervals, Set.mem_iUnion, Set.mem_Ico, exists_prop]

end DomainTheory.NeighbourhoodSystems
