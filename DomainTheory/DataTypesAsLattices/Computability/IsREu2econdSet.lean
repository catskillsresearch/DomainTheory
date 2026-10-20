/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasZero
import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasPos


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.condSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (condSet z x y) := by
  have hleft : REPred fun n => n ∈ x ∧ 0 ∈ z :=
    REPred.and hx (IsRE.hasZero hz)
  have hright : REPred fun n => n ∈ y ∧ ∃ k, k + 1 ∈ z :=
    REPred.and hy (IsRE.hasPos hz)
  exact _root_.REPred.of_eq (REPred.or hleft hright) fun n => Iff.rfl

end DomainTheory.DataTypesAsLattices
