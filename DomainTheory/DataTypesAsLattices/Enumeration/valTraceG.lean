module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceG (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, e.1 = 0 → e.2.1 ∈ Gcomb

end DomainTheory.DataTypesAsLattices
