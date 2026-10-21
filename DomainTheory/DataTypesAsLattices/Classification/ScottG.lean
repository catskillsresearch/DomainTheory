/-ai
The class Scott G is the class of Scott-open subsets of Pω.
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

def ScottG : Set (Set Pomega) := {U | IsScottOpen U}

end DomainTheory.DataTypesAsLattices
