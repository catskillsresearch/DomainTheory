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
import DomainTheory.DataTypesAsLattices.Computability.primrecRel_Scomb_bit


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecPred_Scomb_subset :
    PrimrecPred fun p : ℕ × ℕ =>
      ∀ i < p.1, p.1.testBit i = false ∨
        i ∈ e (pack4_proj2 p.2) ⬝ e (pack4_proj3 p.2) :=
  (primrecRel_Scomb_bit.forall_lt.comp Primrec.fst
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => by
      simp [Nat.unpair_pair]

end DomainTheory.DataTypesAsLattices
