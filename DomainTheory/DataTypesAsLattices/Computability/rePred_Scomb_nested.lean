/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
import DomainTheory.DataTypesAsLattices.Computability.primrecRel_Scomb_app


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem rePred_Scomb_nested :
    REPred fun t : ℕ =>
      pack4_proj4 t ∈
        (e (pack4_proj1 t) ⬝ e (pack4_proj3 t)) ⬝
          (e (pack4_proj2 t) ⬝ e (pack4_proj3 t)) :=
  (REPred.exists (p := fun t k =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t))
    (primrecRel_Scomb_app.swap.computablePred.to_re)).of_eq fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
