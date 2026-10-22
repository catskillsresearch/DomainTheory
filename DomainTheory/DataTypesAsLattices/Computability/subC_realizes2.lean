module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_sub
public import DomainTheory.DataTypesAsLattices.Computability.subC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem subC_realizes2 : Realizes2 subC fun n m => n - m := fun n m => by
  simp [subC_app, primRecComb_ofNat, primRecVal_sub]

end DomainTheory.DataTypesAsLattices
