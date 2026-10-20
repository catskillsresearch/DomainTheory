/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term_interp


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













































theorem Rterm_interp : interp Rterm (fun _ => botElem) = Rcomb := by
  unfold Rterm Rcomb
  apply congrArg graph
  funext x
  change interp (seq2Term .zero (.var 0)) (envSet (fun _ => botElem) 0 x) =
    seq2 (ofNat 0) x
  rw [seq2Term_interp]
  · simp [interp, envSet, Function.update]
  · trivial
  · exact Nat.zero_ne_add_one 7

end DomainTheory.DataTypesAsLattices
