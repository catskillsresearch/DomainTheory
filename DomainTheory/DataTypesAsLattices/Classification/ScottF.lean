module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def ScottF : Set (Set Pomega) := {U | IsScottOpen Uᶜ}

end DomainTheory.DataTypesAsLattices
