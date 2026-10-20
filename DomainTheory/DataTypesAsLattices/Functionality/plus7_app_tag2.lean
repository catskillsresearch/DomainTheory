/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_tag2 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_ofNat_succ, dcondSet_ofNat_one,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
