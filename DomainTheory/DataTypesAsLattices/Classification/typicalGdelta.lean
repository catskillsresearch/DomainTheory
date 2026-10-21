/-ai
The typical 𝔊δ set is the singleton whose only element is ⊤.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalGdelta : Set Pomega := {topElem}

end DomainTheory.DataTypesAsLattices
