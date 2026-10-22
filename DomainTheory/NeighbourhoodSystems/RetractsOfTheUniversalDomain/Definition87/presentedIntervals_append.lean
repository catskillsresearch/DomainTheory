/-ai
The set presented by the concatenation of two lists of endpoint pairs is the union of the sets presented by the lists.

The proof is by induction on the first list. The empty list simplifies, and the step that adjoins a pair uses the cons identity together with associativity of union.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem presentedIntervals_append (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (L1 ++ L2) = presentedIntervals L1 ∪ presentedIntervals L2 := by
  induction L1 with
  | nil => simp
  | cons p L1 ih => simp [List.cons_append, presentedIntervals_cons, ih, Set.union_assoc]

end DomainTheory.NeighbourhoodSystems
