/-ai
If an element x of Pω is recursively enumerable, then so is its predecessor, the set of k such that k + 1 lies in x.

Membership in the predecessor is the membership predicate of x precomposed with the primitive recursive successor, and the two predicates agree definitionally.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.predSet {x : Pomega} (hx : IsRE x) : IsRE (predSet x) :=
  ⟨REPred.of_eq (hx.out.comp Primrec.succ.to_comp) fun _ => Iff.rfl⟩

end DomainTheory.DataTypesAsLattices
