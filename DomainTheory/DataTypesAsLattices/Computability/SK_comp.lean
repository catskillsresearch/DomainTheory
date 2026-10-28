module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem SK_comp (f g x : Pomega) :
    (Scomb ⬝ (Kcomb ⬝ f) ⬝ g) ⬝ x = f ⬝ (g ⬝ x) := by
  rw [Scomb.beta3, Kcomb.beta2]

end DomainTheory.DataTypesAsLattices
