/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC_app
import DomainTheory.DataTypesAsLattices.Computability.sqrtIter_self
import DomainTheory.DataTypesAsLattices.Computability.primRecVal_sqrt


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
