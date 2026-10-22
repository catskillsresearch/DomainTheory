/-ai
The universal neighbourhood system on the rationals takes as its neighbourhoods the universal family, as its master the half-open unit interval, and as its structure laws the nonemptiness of that interval, its membership in the family, closure of the family under intersection, and containment of every member in the master.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMaster
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_master_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMaster_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_inter_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_sub_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Definition 8.7 (Scott 1981, PRG-19).** The neighbourhood system `𝒰` over `[0,1) ⊆ ℚ`: its
neighbourhoods are the non-empty subsets of `[0,1)` presentable as a finite union of rational
intervals `[r,s)` (see the module docstring for why the raw endpoints need no `0 ≤ r < s ≤ 1`
side-condition, and `mem_iff_scott` for the literal reconciliation). Proof fields are named
theorems so Palomar can lock this value without generated `._proof_N` constants. -/
def U : NeighborhoodSystem ℚ where
  mem := UMem
  master := UMaster
  master_nonempty := UMaster_nonempty
  master_mem := U_master_mem
  inter_mem := U_inter_mem
  sub_master := U_sub_master

end DomainTheory.NeighbourhoodSystems
