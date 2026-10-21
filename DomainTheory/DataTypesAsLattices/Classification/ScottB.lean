/-ai
The class Scott B is the class of Boolean-open subsets of Pω.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def ScottB : Set (Set Pomega) := {U | IsBooleanOpen U}

end DomainTheory.DataTypesAsLattices
