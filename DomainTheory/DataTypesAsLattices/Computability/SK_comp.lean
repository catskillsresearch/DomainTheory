module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem SK_comp (f g x : Pomega) :
    (Scomb ⬝ (Kcomb ⬝ f) ⬝ g) ⬝ x = f ⬝ (g ⬝ x) := by
  rw [Scomb_beta3, Kcomb_beta2]

end DomainTheory.DataTypesAsLattices
