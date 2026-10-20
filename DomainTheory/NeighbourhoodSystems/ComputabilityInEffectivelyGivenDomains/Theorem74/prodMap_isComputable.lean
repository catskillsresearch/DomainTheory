/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.Exercise319
public import DomainTheory.Neighborhood.Exercise319Sum
public import DomainTheory.Neighborhood.Theorem74.Basic
public import DomainTheory.Neighborhood.Theorem74.proju2080_isComputable
public import DomainTheory.Neighborhood.Theorem74.proju2081_isComputable
public import DomainTheory.Neighborhood.Theorem74.paired_isComputable

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





/-- **Theorem 7.4 (Scott 1981, PRG-19) — the product functor `f × g` is computable.** Using
`f × g = ⟨f ∘ p₀, g ∘ p₁⟩` (Exercise 3.19) together with computability of `projᵢ` and `comp`
(Proposition 7.3). -/
theorem prodMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₀' : ComputablePresentation V₀'} {P₁' : ComputablePresentation V₁'}
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMap P₀ P₀' f) (hg : IsComputableMap P₁ P₁' g) :
    IsComputableMap (prodPresentation P₀ P₁) (prodPresentation P₀' P₁') (prodMap f g) := by
  rw [prodMap]
  exact paired_isComputable (comp_isComputable (proj₀_isComputable P₀ P₁) hf)
    (comp_isComputable (proj₁_isComputable P₀ P₁) hg)

end DomainTheory.Neighborhood
