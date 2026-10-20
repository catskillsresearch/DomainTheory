module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def oddEvenPack (f g : Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | (∃ n, k = 2 * n + 1 ∧ n ∈ f x) ∨ (∃ n, k = 2 * n ∧ n ∈ g x)}

end DomainTheory.DataTypesAsLattices
