module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsScottGdelta (U : Set Pomega) : Prop :=
  ∃ Us : ℕ → Set Pomega, (∀ n, IsScottOpen (Us n)) ∧ U = ⋂ n, Us n

end DomainTheory.DataTypesAsLattices
