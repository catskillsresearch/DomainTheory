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
import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





















































theorem Rcomb_mem_FUN : Rcomb ∈ FUN :=
  graph_mem_FUN (seq2_right_isScottContinuous (ofNat 0))

end DomainTheory.DataTypesAsLattices
