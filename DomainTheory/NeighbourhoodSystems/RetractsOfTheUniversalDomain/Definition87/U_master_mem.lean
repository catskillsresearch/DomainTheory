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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMaster

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- `[0,1)` is presented by the single interval `[0,1)`. -/
theorem U_master_mem : UMem UMaster :=
  ⟨⟨[(0, 1)], by rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]⟩,
    ⟨0, by norm_num⟩, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems
