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
import DomainTheory.DataTypesAsLattices.Computability.mulC_app
import DomainTheory.DataTypesAsLattices.Computability.primRecVal_mul


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4













theorem mulC_realizes2 : Realizes2 mulC fun n m => n * m := fun n m => by
  simp [mulC_app, primRecComb_ofNat, primRecVal_mul]

end DomainTheory.DataTypesAsLattices
