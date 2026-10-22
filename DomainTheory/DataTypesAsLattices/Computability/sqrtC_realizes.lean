/-ai
The combinator sqrtC realizes the natural-number square root.

Unfold sqrtC and apply the S-combinator law Scomb_beta3 three times and the K-combinator law Kcomb_beta2 twice. The identities primRecZeroC_app, primRecComb_ofNat, primRecVal_sqrt, and sqrtIter_self then give the numeral of the square root.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC_app
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter_self
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_sqrt

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem sqrtC_realizes : Realizes sqrtC Nat.sqrt := fun n => by
  rw [sqrtC, Scomb_beta3, Scomb_beta3, Scomb_beta3, Kcomb_beta2, Kcomb_beta2,
    primRecZeroC_app, primRecComb_ofNat,
    primRecVal_sqrt, sqrtIter_self]

end DomainTheory.DataTypesAsLattices
