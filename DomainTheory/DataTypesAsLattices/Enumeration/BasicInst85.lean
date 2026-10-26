module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

instance : DecidableRel beforeHalt :=
  fun m j => decidable_of_iff (∀ i : Fin (j + 1), haltEnum i.val ≠ m)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.isLt⟩

end DomainTheory.DataTypesAsLattices
