/-ai
The top element of Pω, the set of all natural numbers, is recursively enumerable.

The constantly true predicate is recursively enumerable, and simplification shows that it is membership in the top element.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2etrue

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.top : IsRE topElem :=
  REPred.true.of_eq fun n => by simp [topElem]

end DomainTheory.DataTypesAsLattices
