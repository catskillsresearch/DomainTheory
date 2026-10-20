/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem seq2_app_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
