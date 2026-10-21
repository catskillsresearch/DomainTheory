/-ai
The conditional of three recursively enumerable sets is recursively enumerable.

Membership in the conditional is the disjunction of membership in the first branch together with membership of zero in the condition, and membership in the second branch together with the existence of a positive element of the condition. Both sides of the disjunction are recursively enumerable, using that membership of zero and the existence of a positive element are recursively enumerable predicates, and the disjunction is exactly the membership predicate of the conditional.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasZero
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasPos

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.condSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (condSet z x y) := by
  have hleft : REPred fun n => n ∈ x ∧ 0 ∈ z :=
    REPred.and hx (IsRE.hasZero hz)
  have hright : REPred fun n => n ∈ y ∧ ∃ k, k + 1 ∈ z :=
    REPred.and hy (IsRE.hasPos hz)
  exact _root_.REPred.of_eq (REPred.or hleft hright) fun n => Iff.rfl

end DomainTheory.DataTypesAsLattices
