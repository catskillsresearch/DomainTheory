/-ai
The zero-characteristic map of a set U sends an element x to the set of those indices that equal zero and for which some finite piece of x already lies in U. Thus zero lies in the value precisely when some finite piece of x lies in U.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Characteristic-style map used in Theorem 6.1: `0 ∈ f(x)` iff some
finite piece of `x` already lies in `U`. -/
def charOpen (U : Set Pomega) (x : Pomega) : Pomega :=
  {k | k = 0 ∧ ∃ n, e n ⊆ x ∧ e n ∈ U}

end DomainTheory.DataTypesAsLattices
