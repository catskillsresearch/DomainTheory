module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_master_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_inter_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4_sub_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem


/-- The neighbourhoods of Example 1.5 are a finite family, hence countable. -/
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} :=
  inferInstance
end DomainTheory.NeighbourhoodSystems.Example15
