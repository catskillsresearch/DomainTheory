/-ai
A valuation trace is structurally justified when every one of its entries is justified in that trace.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceStruct (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, valEntryJustified tr e

end DomainTheory.DataTypesAsLattices
