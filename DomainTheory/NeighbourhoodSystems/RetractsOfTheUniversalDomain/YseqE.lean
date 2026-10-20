module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE_zero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α γ : Type*}

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

variable (X : ℕ → Set α) (Δ : Set α)

variable (hΔ : Δ.Nonempty) (hEmne : E.master.Nonempty) (hsplit : SplitSpec' E split)

include hΔ hEmne hsplit

omit hΔ hEmne hsplit in
/-- **The abstract analogue of Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the
"+"-piece chosen when splitting against `X n`. Generalizes `Theorem88.lean`'s `Yseq`. -/
noncomputable def YseqE (n : ℕ) : Set γ :=
  ⋃ δ' : Fin n → Bool, atomE E split X Δ (extendTrue δ') (n + 1)

end DomainTheory.NeighbourhoodSystems
