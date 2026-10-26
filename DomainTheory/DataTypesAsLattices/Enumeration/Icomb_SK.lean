module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def Icomb_SK : Pomega := funOf (funOf Scomb Kcomb) Kcomb

namespace Icomb_SK

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (x : Pomega) : funOf Icomb_SK x = x := by
  rw [Icomb_SK, Scomb.beta3, Kcomb.beta2]

end Icomb_SK

end DomainTheory.DataTypesAsLattices
