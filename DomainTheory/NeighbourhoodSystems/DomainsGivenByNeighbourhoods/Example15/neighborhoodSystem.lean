/-ai
Scott's Example 1.5 is the neighbourhood system of all nonempty subsets of the four-element token set. Membership is nonemptiness, the master neighbourhood is the whole token set, and the system laws are the facts that this master is nonempty and a neighbourhood, that a nonempty witness inside an intersection makes the intersection a neighbourhood, and that every set of tokens is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_inter_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_sub_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- **Example 1.5.** The neighbourhood system of all non-empty subsets of `Δ = {0,1,2,3}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master := master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master

end DomainTheory.NeighbourhoodSystems.Example15
