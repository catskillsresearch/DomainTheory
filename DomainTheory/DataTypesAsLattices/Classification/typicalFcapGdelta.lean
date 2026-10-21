/-ai
The typical 𝔉 ∩ 𝔊δ set is the singleton whose only element is ⊤ + 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalFcapGdelta : Set Pomega := {succSet topElem}

end DomainTheory.DataTypesAsLattices
