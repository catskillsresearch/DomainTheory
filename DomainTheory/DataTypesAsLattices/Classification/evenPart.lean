/-ai
The even part of an element y of Pω is the set of natural numbers n such that 2n belongs to y.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def evenPart (y : Pomega) : Pomega := {n | 2 * n ∈ y}

end DomainTheory.DataTypesAsLattices
