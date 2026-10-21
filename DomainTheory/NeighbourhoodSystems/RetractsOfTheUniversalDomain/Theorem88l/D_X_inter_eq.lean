/-ai
The enumerated neighbourhood at the list-code intersection of two codes equals the neighbourhood presented at the fold of the second decoded list, started at the code-level fold of the first code.

The left side is the neighbourhood at the code-level fold of the appended codes. The code-fold equation and the append equation rewrite it as the fold of the concatenated decoded lists from the master index. The fold of the first decoded list from the master index is the code-level fold of the first code, by symmetry of the code-fold equation. The append equation for left folds then starts the second fold at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}




variable (P qChar cons)

variable {P qChar cons}

theorem D_X_inter_eq (c₁ c₂ : ℕ) :
    D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) (myFoldCode P qChar cons c₁)) := by
  have h1 : D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₁ ++ decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons (appendListCode c₁ c₂)) = _
    rw [myFoldCode_eq, appendListCode_eq]
    rfl
  have heq1 : (decodeList c₁).foldl (myStep P qChar cons) P.masterIdx =
      myFoldCode P qChar cons c₁ := (myFoldCode_eq P qChar cons c₁).symm
  rw [h1, List.foldl_append, heq1]

end DomainTheory.NeighbourhoodSystems
