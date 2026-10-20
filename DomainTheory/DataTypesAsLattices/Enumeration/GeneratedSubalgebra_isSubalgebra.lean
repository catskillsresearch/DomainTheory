/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem GeneratedSubalgebra_isSubalgebra (xs : List Pomega) :
    IsSubalgebra (GeneratedSubalgebra xs) := by
  constructor
  · intro A hA _
    exact hA.1
  · intro u v hu hv A hA hxs
    exact hA.2 (hu A hA hxs) (hv A hA hxs)

end DomainTheory.DataTypesAsLattices
