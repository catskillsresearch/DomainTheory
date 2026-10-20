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
import DomainTheory.DataTypesAsLattices.Enumeration.seq2_mem_subalgebra


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem packList_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A) :
    ∀ {xs : List Pomega}, (∀ x, x ∈ xs → x ∈ A) → packList xs ∈ A
  | [], _ => combinatory_mem_subalgebra hA bot_combinatory
  | x :: xs, hxs =>
      seq2_mem_subalgebra hA (hxs x (by simp))
        (packList_mem_subalgebra hA fun y hy => hxs y (by simp [hy]))

end DomainTheory.DataTypesAsLattices
