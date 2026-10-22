module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Membership: the non-empty subsets of `Δ`. -/
def P4Mem (X : Set Token) : Prop := X.Nonempty

end DomainTheory.NeighbourhoodSystems.Example15
