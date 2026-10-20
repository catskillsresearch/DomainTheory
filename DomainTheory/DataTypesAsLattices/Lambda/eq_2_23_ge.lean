/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.seq2_app


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_23_ge (x y : Pomega) (n : ℕ) :
    funOf (seq2 x y) (ofNat (n + 2)) = botElem := by
  rw [seq2_app]
  ext k
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
