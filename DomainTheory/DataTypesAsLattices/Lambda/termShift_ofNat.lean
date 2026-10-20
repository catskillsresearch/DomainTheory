/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.succSet_ofNat
import DomainTheory.DataTypesAsLattices.Lambda.termShift_app


namespace DomainTheory.DataTypesAsLattices



















































theorem termShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (termShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [termShift_app, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
