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
import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.packList_cons_zero
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_finite
import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_Deg


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































/-- **Scott 1976, Theorem 3.6 converse (singleton).** The packed
generator recovers `x` in its own degree. -/
theorem theorem_3_6_converse (x : Pomega) :
    x ∈ Deg (singleGenerator [x]) := by
  have hp := (theorem_3_6_finite [x]).1
  have h0 := combinatory_mem_Deg (singleGenerator [x]) (ofNat_combinatory 0)
  have : funOf (packList [x]) (ofNat 0) ∈ Deg (singleGenerator [x]) :=
    (Deg_isSubalgebra _).2 hp h0
  simpa [packList_cons_zero] using this

end DomainTheory.DataTypesAsLattices
