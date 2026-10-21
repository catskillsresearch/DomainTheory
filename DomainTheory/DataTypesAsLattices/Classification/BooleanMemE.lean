/-ai
A set admits a Boolean membership witness when a Scott-continuous map sends every element into the numbers below a fixed bound, and the set is the preimage of a finite collection of elements that themselves lie below that bound.
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

/-- Witness used in the inductive proof of Theorem 6.6. -/
def BooleanMemE (U : Set Pomega) : Prop :=
  ∃ (f : Pomega → Pomega) (N : ℕ) (E : Set Pomega),
    IsScottContinuous f ∧
      (∀ x, f x ⊆ {m | m < N}) ∧
        E.Finite ∧ (∀ e ∈ E, e ⊆ {m | m < N}) ∧
          U = {x | f x ∈ E}

end DomainTheory.DataTypesAsLattices
