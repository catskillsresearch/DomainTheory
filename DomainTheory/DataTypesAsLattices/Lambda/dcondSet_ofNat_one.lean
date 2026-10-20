/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_ofNat_one (x y : Pomega) : dcondSet (ofNat 1) x y = y := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

end DomainTheory.DataTypesAsLattices
