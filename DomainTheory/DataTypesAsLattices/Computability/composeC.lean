module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def composeC (u v : Pomega) : Pomega :=
  funOf (funOf Scomb (funOf Kcomb u)) v

namespace composeC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (composeC u v) :=
  .app (.app .S (.app .K hu)) hv

theorem realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (composeC u v) (p ∘ q) := fun n => by
  rw [composeC, Scomb.beta3, Kcomb.beta2, hv n, hu (q n)]
  rfl

end composeC

end DomainTheory.DataTypesAsLattices
