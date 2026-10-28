module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pairComb

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pairRealizer (u v : Pomega) : Pomega :=
  Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ pairComb) ⬝ u) ⬝ v

namespace pairRealizer

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (pairRealizer u v) :=
  .app (.app .S (.app (.app .S (.app .K pairComb.combinatory)) hu)) hv

theorem realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (pairRealizer u v) (fun n => Nat.pair (p n) (q n)) := fun n => by
  rw [pairRealizer, Scomb.beta3, Scomb.beta3, Kcomb.beta2,
    hu, hv, pairComb.app]

end pairRealizer

end DomainTheory.DataTypesAsLattices
