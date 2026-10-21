/-ai
Scott's table u, given on {⊥, 0, ⊤} and extended continuously to all of Pω, sends a pair (x, y) to the set of k such that either k is 0 and x or y is nonempty, or k is 1 and either 0 lies in x while some successor lies in y, or some successor lies in x while 0 lies in y.
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

/-- Scott's table `u` on `{⊥, 0, ⊤}`, extended continuously to all of `Pω`. -/
def uvU (x y : Pomega) : Pomega :=
  {k | (k = 0 ∧ (x.Nonempty ∨ y.Nonempty)) ∨
       (k = 1 ∧ ((0 ∈ x ∧ ∃ n, n + 1 ∈ y) ∨ ((∃ n, n + 1 ∈ x) ∧ 0 ∈ y)))}

end DomainTheory.DataTypesAsLattices
