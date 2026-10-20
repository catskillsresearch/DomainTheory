module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.mulC_app
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_mul

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4













theorem mulC_realizes2 : Realizes2 mulC fun n m => n * m := fun n m => by
  simp [mulC_app, primRecComb_ofNat, primRecVal_mul]

end DomainTheory.DataTypesAsLattices
