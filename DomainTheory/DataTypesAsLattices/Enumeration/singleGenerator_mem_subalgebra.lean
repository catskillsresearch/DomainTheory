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
import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.packList_mem_subalgebra


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem singleGenerator_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {xs : List Pomega} (hxs : ∀ x, x ∈ xs → x ∈ A) :
    singleGenerator xs ∈ A := by
  have hc := combinatory_mem_subalgebra hA IsCombinatory.cond
  exact hA.2 (hA.2 hc (packList_mem_subalgebra hA hxs)) hA.1

end DomainTheory.DataTypesAsLattices
