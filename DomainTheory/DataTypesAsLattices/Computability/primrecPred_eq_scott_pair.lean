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
import DomainTheory.DataTypesAsLattices.Computability.primrec_pair


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecPred_eq_scott_pair :
    PrimrecPred fun t : ℕ × ℕ × ℕ => t.1 = pair t.2.1 t.2.2 :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

end DomainTheory.DataTypesAsLattices
