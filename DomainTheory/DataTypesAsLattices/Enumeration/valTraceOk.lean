module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceG

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceOk (tr : ValTrace) : Prop :=
  valTraceStruct tr ∧ valTraceG tr

end DomainTheory.DataTypesAsLattices
