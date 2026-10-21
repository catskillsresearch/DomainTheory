/-ai
The typical 𝔊 set is the set of elements x of Pω such that 0 belongs to x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalG : Set Pomega := {x | 0 ∈ x}

end DomainTheory.DataTypesAsLattices
