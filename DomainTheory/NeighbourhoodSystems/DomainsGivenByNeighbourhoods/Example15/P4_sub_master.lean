module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Every neighbourhood is a subset of `Δ`. -/
theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master :=
  Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Example15
