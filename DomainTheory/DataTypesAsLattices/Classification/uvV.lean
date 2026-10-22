/-ai
Scott's table v, given on {⊥, 0, ⊤} and extended continuously to all of Pω, sends a pair (x, y) to the set of k such that k is 0, or k is 1 and some successor lies in x or in y, or else both 0 and some successor lie in x and both lie in y, in which case every k belongs.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Scott's table `v` on `{⊥, 0, ⊤}`, extended continuously to all of `Pω`. -/
def uvV (x y : Pomega) : Pomega :=
  {k | k = 0 ∨
       (k = 1 ∧ ((∃ n, n + 1 ∈ x) ∨ (∃ n, n + 1 ∈ y))) ∨
       (0 ∈ x ∧ (∃ n, n + 1 ∈ x) ∧ 0 ∈ y ∧ (∃ n, n + 1 ∈ y))}

end DomainTheory.DataTypesAsLattices
