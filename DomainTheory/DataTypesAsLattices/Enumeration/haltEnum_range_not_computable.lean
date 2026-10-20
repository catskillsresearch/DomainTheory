/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum_succ_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code















theorem haltEnum_range_not_computable :
    ¬ComputablePred fun m => ∃ t, haltEnum t = m := by
  intro hc
  have := hc.choose
  have hsucc : ComputablePred fun n : ℕ => ∃ t, haltEnum t = n + 1 :=
    Computable.computablePred
      ((ComputablePred.decide hc).comp Primrec.succ.to_comp)
  have hn : ComputablePred fun n : ℕ =>
      (eval (Denumerable.ofNat Code n) 0).Dom :=
    hsucc.of_eq fun n => haltEnum_succ_iff n
  have := hn.choose
  have : DecidablePred fun c : Code => (eval c 0).Dom :=
    fun c => decidable_of_iff
      (eval (Denumerable.ofNat Code (encode c)) 0).Dom
      (by simp [Denumerable.ofNat_encode])
  exact ComputablePred.halting_problem (n := 0)
    (Computable.computablePred
      ((ComputablePred.decide hn).comp Computable.encode |>.of_eq fun c => by
        simp [Denumerable.ofNat_encode]))

end DomainTheory.DataTypesAsLattices
