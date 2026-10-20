module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsBdelta (U : Set Pomega) : Prop :=
  ∃ Bs : ℕ → Set Pomega, (∀ n, IsBooleanOpen (Bs n)) ∧ U = ⋂ n, Bs n

end DomainTheory.DataTypesAsLattices
