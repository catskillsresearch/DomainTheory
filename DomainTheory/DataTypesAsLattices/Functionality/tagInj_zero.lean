/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero


namespace DomainTheory.DataTypesAsLattices
































theorem tagInj_zero (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 0) = ofNat i :=
  pairSeq_app_zero (ofNat i) x

end DomainTheory.DataTypesAsLattices
