/-ai
The predicate that a valuation trace is well formed is recursively enumerable.

It is the conjunction of the primitive recursive structural predicate, read as a recursively enumerable predicate, and the recursively enumerable G predicate. The conjunction agrees with well-formedness.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceG_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem valTraceOk_re : REPred valTraceOk :=
  _root_.REPred.of_eq
    (REPred.and primrecPred_valTraceStruct.computablePred.to_re valTraceG_re)
    fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
