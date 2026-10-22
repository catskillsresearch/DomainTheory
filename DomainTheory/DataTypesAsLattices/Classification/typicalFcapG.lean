/-ai
The typical 𝔉 ∩ 𝔊 set is the singleton whose only element is the singleton {0}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalFcapG : Set Pomega := {ofNat 0}

end DomainTheory.DataTypesAsLattices
