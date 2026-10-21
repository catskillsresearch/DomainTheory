/-ai
The class Scott F is the class of Scott-closed subsets of Pω, the complements of the Scott-open sets.
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

def ScottF : Set (Set Pomega) := {U | IsScottOpen Uᶜ}

end DomainTheory.DataTypesAsLattices
