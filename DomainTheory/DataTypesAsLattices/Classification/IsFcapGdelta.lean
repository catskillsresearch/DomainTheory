/-ai
A set is a closed-and-Gδ intersection when it is the intersection of a Scott-closed set and a countable intersection of Scott-open sets.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen
public import DomainTheory.DataTypesAsLattices.Classification.IsScottGdelta

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsFcapGdelta (U : Set Pomega) : Prop :=
  ∃ C G, IsScottOpen Cᶜ ∧ IsScottGdelta G ∧ U = C ∩ G

end DomainTheory.DataTypesAsLattices
