/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag3 (H x t : Pomega) :
    Hstep H (tagInj 3 x) t = hPred H (tagInj 3 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_self,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
