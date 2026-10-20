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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






































theorem seq2_left_isScottContinuous (b : Pomega) :
    IsScottContinuous (fun a => seq2 a b) :=
  graph_const_isScottContinuous
    (fun a z => condSet z a (condSet (predSet z) b botElem))
    (fun z => condSet_isScottContinuous_mid z _)

end DomainTheory.DataTypesAsLattices
