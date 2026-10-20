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
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredSet
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_primrecRel


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.predC : IsRE predC := by
  have hp : PrimrecRel fun n m : ℕ => n.testBit (m + 1) = true :=
    primrecPred_bool (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.succ.comp Primrec.snd))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.predSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro h; exact mem_e.mpr h
    · intro h; exact mem_e.mp h
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
