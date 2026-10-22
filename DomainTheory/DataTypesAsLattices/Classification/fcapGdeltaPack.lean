/-ai
The packing of two maps f and g at an element x of Pω contains 0 precisely when 0 belongs to f(x), and contains a successor n + 1 precisely when n belongs to g(x).
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def fcapGdeltaPack (f g : Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | (k = 0 ∧ 0 ∈ f x) ∨ ∃ n, k = n + 1 ∧ n ∈ g x}

end DomainTheory.DataTypesAsLattices
