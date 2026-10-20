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
import DomainTheory.DataTypesAsLattices.Computability.primRecVal_add
import DomainTheory.DataTypesAsLattices.Computability.addC_app


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4









theorem addC_realizes2 : Realizes2 addC fun n m => n + m := fun n m => by
  simp [addC_app, primRecComb_ofNat, primRecVal_add]

end DomainTheory.DataTypesAsLattices
