/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.hasPos {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => ∃ k, k + 1 ∈ z :=
  _root_.REPred.of_eq
    (REPred.exists (p := fun _ k => k + 1 ∈ z)
      (hz.comp (Primrec.succ.to_comp.comp Computable.snd)))
    fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
