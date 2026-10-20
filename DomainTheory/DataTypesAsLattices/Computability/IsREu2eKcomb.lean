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
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_re
import DomainTheory.DataTypesAsLattices.Computability.mem_graph_const_iff


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.Kcomb : IsRE Kcomb :=
  IsRE.graph_of_re (f := fun x => graph (fun _ => x)) <| by
    have hP : PrimrecPred fun w : ℕ × ℕ =>
        (Nat.unpair w.1).2 = pair (Nat.unpair w.2).1 (Nat.unpair w.2).2 ∧
          (Nat.unpair w.1).1.testBit (Nat.unpair w.2).2 = true :=
      (Primrec.eq.comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
          (primrec_pair.comp
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).and
        (primrecPred_bool (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    have hex : REPred fun w : ℕ =>
        ∃ t, (Nat.unpair w).2 = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
          (Nat.unpair w).1.testBit (Nat.unpair t).2 = true :=
      REPred.exists hP.computablePred.to_re
    exact _root_.REPred.of_eq
      (hex.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd).to_comp)
      fun q => by
        simp only [Nat.unpair_pair]
        exact (mem_graph_const_iff q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
