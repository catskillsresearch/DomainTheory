/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Exercise715.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510



section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)



theorem osum_mem_iff {W : Set (Option (α ⊕ β))} :
    (osum h₀ h₁).mem W ↔ W = sumMaster V₀ V₁ ∨
      (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
      (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y) := Iff.rfl

end Coalesced
end DomainTheory.Neighborhood
