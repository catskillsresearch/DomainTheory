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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem seq2_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {x y : Pomega} (hx : x ∈ A) (hy : y ∈ A) : seq2 x y ∈ A := by
  have hS := combinatory_mem_subalgebra hA IsCombinatory.S
  have hK := combinatory_mem_subalgebra hA IsCombinatory.K
  have hcond := combinatory_mem_subalgebra hA IsCombinatory.cond
  have hpred := combinatory_mem_subalgebra hA IsCombinatory.pred
  have hzero := combinatory_mem_subalgebra hA IsCombinatory.zero
  have hbot := combinatory_mem_subalgebra hA bot_combinatory
  have hcondx := hA.2 hcond hx
  have hyb := hA.2 (hA.2 hcond hy) (hA.2 hpred hzero)
  have hinter := hA.2 (hA.2 hS (hA.2 hK hyb)) hpred
  have hF := hA.2 (hA.2 hS (hA.2 hK hcondx)) hinter
  have hI := hA.2 (hA.2 hS hK) hK
  rw [seq2_eq_SK]
  exact hA.2 (hA.2 hS hF) hI

end DomainTheory.DataTypesAsLattices
