/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag0 (H x t : Pomega) :
    Hstep H (tagInj 0 x) t = funOf t x := by
  simp only [Hstep, expTag, expPayload, hVar, tagInj_zero, tagInj_one,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
