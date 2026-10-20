/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38
import DomainTheory.DataTypesAsLattices.Functionality.typed_bot_bot


namespace DomainTheory.DataTypesAsLattices






























/-- **Scott 1976, after (4.38).** The atom `⟨0⟩ : tree`. -/
theorem tree_atom : typed (pairSeq (ofNat 0) botElem) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inl typed_bot_bot

end DomainTheory.DataTypesAsLattices
