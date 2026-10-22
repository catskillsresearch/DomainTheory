/-ai
If a nonempty set of tokens is contained in an intersection, then the intersection is nonempty.

The nonempty witness of the smaller set remains a witness of the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- A non-empty witness inside `X ∩ Y` shows the intersection is a neighbourhood. -/
theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) :=
  hZ.mono hZsub

end DomainTheory.NeighbourhoodSystems.Example15
