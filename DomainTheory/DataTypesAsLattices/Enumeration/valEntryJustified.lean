/-ai
An entry of a valuation trace, a code together with a member and a time stamp, is justified when the code is zero, or else the trace records the pair of the time stamp with the member at the operator component of the unpairing of the predecessor of the code, and for every index below the time stamp plus one either that bit of the time stamp is false or the trace records the index at the argument component of that unpairing.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valEntryJustified (tr : ValTrace) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 = 0 ∨
    (valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) ∧
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i)

end DomainTheory.DataTypesAsLattices
