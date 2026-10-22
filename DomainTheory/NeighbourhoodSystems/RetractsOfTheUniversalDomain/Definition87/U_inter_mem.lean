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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.combineIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Intersection of two presentable sets is presentable, via `combineIntervals`. -/
theorem U_inter_mem {X Y Z : Set ℚ} (hX : UMem X) (hY : UMem Y) (hZ : UMem Z)
    (hZsub : Z ⊆ X ∩ Y) : UMem (X ∩ Y) := by
  rcases hX with ⟨⟨L1, rfl⟩, -, hXsub⟩
  rcases hY with ⟨⟨L2, rfl⟩, -, -⟩
  rcases hZ with ⟨-, hZne, -⟩
  exact ⟨⟨combineIntervals L1 L2, presentedIntervals_inter L1 L2⟩,
    hZne.mono hZsub, Set.inter_subset_left.trans hXsub⟩

end DomainTheory.NeighbourhoodSystems
