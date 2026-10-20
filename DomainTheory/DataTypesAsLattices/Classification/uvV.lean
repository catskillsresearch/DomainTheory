module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Scott's table `v` on `{⊥, 0, ⊤}`, extended continuously to all of `Pω`. -/
def uvV (x y : Pomega) : Pomega :=
  {k | k = 0 ∨
       (k = 1 ∧ ((∃ n, n + 1 ∈ x) ∨ (∃ n, n + 1 ∈ y))) ∨
       (0 ∈ x ∧ (∃ n, n + 1 ∈ x) ∧ 0 ∈ y ∧ (∃ n, n + 1 ∈ y))}

end DomainTheory.DataTypesAsLattices
