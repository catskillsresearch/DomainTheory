/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_testBit : PrimrecRel fun n k : ℕ => n.testBit k = true :=
  primrecPred_bool (f := fun p : ℕ × ℕ => p.1.testBit p.2) primrec_testBit

end DomainTheory.DataTypesAsLattices
