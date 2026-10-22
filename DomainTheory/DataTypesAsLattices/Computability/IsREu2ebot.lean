/-ai
The empty set is recursively enumerable.

The empty predicate is recursively enumerable, and it agrees with membership in the empty set.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eempty

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.bot : IsRE botElem :=
  ⟨REPred.empty.of_eq fun n => by simp [botElem]⟩

end DomainTheory.DataTypesAsLattices
