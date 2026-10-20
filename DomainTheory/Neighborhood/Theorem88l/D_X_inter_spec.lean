/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88k
import DomainTheory.Neighborhood.Theorem88l.Basic
import DomainTheory.Neighborhood.Theorem88l.myFoldl_inter_of_le
import DomainTheory.Neighborhood.Theorem88l.D_X_inter_eq


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}




variable (P qChar cons)

variable {P qChar cons}

/-- **Theorem 8.8(c), Part 5 of 6, headline.** Given `D`-consistency of `c₁`, `c₂`,
`D_X (D_inter c₁ c₂) = D_X c₁ ∩ D_X c₂`. The hypothesis is already stated at the `V`-side (`D_X`'s
codomain *is* `P.X` of a raw index), so `myFoldl_inter_of_le` applies directly with `n :=
myFoldCode c₁`, `r := P.masterIdx`. -/
theorem D_X_inter_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) {c₁ c₂ : ℕ}
    (h : ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) :
    D_X P qChar cons (D_inter c₁ c₂) = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
  have heq2 : D_X P qChar cons c₂ =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons c₂) = _
    rw [myFoldCode_eq]
    rfl
  have hnr : P.X (myFoldCode P qChar cons c₁) ⊆ P.X P.masterIdx := by
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X _)
  have hk : ∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    obtain ⟨k, hk0⟩ := h
    refine ⟨myFoldCode P qChar cons k, ?_⟩
    rw [← heq2]
    exact hk0
  rw [D_X_inter_eq, myFoldl_inter_of_le hcons (decodeList c₂) hnr hk, ← heq2]
  rfl

end DomainTheory.Neighborhood
