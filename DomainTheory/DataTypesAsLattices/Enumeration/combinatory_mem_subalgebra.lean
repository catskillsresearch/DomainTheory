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






















































theorem combinatory_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {u : Pomega} (hu : IsCombinatory u) : u ∈ A := by
  have hgen : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction hgen with
  | G => exact hA.1
  | app _ _ ih ih' => exact hA.2 ih ih'

end DomainTheory.DataTypesAsLattices
