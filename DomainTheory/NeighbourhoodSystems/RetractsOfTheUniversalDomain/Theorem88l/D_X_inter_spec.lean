/-ai
If two list codes are consistent for the induced enumeration, then the enumerated neighbourhood at their list-code intersection equals the intersection of the two enumerated neighbourhoods.

The second enumerated neighbourhood is the neighbourhood at the fold of its decoded list from the master index, by the code-fold equation. The neighbourhood at the first code-level fold is contained in the master neighbourhood by the master-index specification and containment in the master. The consistency hypothesis, rewritten through that description of the second neighbourhood, is a raw consistency witness for the first fold output against the fold from the master. Rewrite by the intersection equation for the enumeration and by the refolding lemma, then restore the description of the second neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myFoldl_inter_of_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_X_inter_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems
