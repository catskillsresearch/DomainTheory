/-ai
A set is a closed-and-open intersection when it is the intersection of a Scott-closed set and a Scott-open set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsFcapG (U : Set Pomega) : Prop :=
  ∃ C O, IsScottOpen Cᶜ ∧ IsScottOpen O ∧ U = C ∩ O

end DomainTheory.DataTypesAsLattices
