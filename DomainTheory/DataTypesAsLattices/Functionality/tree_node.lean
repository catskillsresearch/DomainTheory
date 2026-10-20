/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38


namespace DomainTheory.DataTypesAsLattices






























/-- **Scott 1976, after (4.38).** Binary trees are in `tree`. -/
theorem tree_node {x y : Pomega} (hx : typed x treeR) (hy : typed y treeR) :
    typed (pairSeq (ofNat 1) (pairSeq x y)) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inr ((typed_pairSeq_tensorR treeR treeR x y).mpr ⟨hx, hy⟩)

end DomainTheory.DataTypesAsLattices
