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




theorem minExtend_union (p : ℕ → Pomega) (x y : Pomega) :
    minExtend p (x ∪ y) = minExtend p x ∪ minExtend p y := by
  ext k
  simp [minExtend, or_and_right, exists_or]

end DomainTheory.DataTypesAsLattices
