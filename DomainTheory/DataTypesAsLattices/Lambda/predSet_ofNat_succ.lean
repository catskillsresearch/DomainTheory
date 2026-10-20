/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem predSet_ofNat_succ (n : ℕ) : predSet (ofNat (n + 1)) = ofNat n := by
  ext k
  simp [predSet, ofNat]

end DomainTheory.DataTypesAsLattices
