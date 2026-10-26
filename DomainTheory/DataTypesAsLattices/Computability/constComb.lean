module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def constComb (k : ℕ) : Pomega := funOf Kcomb (ofNat k)

namespace constComb

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory (k : ℕ) : IsCombinatory (constComb k) :=
  .app .K (ofNat.combinatory k)


theorem realizes (k : ℕ) : Realizes (constComb k) fun _ => k := fun _ => by
  simp [constComb, Kcomb.beta2]

end constComb

end DomainTheory.DataTypesAsLattices
