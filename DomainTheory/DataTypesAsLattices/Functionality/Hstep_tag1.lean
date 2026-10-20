/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
