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
import DomainTheory.DataTypesAsLattices.Enumeration.funRetract_combinatory
import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_eq_compose


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





















































theorem enumComp_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (enumComp u v) := by
  rw [enumComp_eq_compose]
  exact .app funRetract_combinatory (composeC_combinatory hu hv)

end DomainTheory.DataTypesAsLattices
