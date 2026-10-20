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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4






































theorem primrec_enumFun (c : Code) : Nat.Primrec (enumFun c) := by
  have heval : Primrec fun t : ℕ => evaln t.unpair.2 c t.unpair.1 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.const c))
        (Primrec.fst.comp Primrec.unpair)
  have h : Primrec fun t : ℕ =>
      bif (evaln t.unpair.2 c t.unpair.1).isSome
        then t.unpair.1 + 1 else 0 :=
    (Primrec.cond (Primrec.option_isSome.comp heval)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun t => by simp [Nat.succ_eq_add_one]
  exact Primrec.nat_iff.mp (h.of_eq fun _ => rfl)

end DomainTheory.DataTypesAsLattices
