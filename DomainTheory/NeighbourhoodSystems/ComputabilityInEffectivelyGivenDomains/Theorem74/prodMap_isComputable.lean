/-ai
The product of two computable maps is computable.

Rewrite the product map as the pairing of the first map after the first projection with the second map after the second projection. Each projection is computable, composition preserves computability, and pairing preserves computability.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.proju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.proju2081_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.paired_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
    (hf : ComputableMap P₀ P₀' f) (hg : ComputableMap P₁ P₁' g) :
    ComputableMap (prodPresentation P₀ P₁) (prodPresentation P₀' P₁') (prodMap f g) := by
  rw [prodMap]
  exact paired_isComputable (comp_isComputable (proj₀_isComputable P₀ P₁) hf)
    (comp_isComputable (proj₁_isComputable P₀ P₁) hg)

end DomainTheory.NeighbourhoodSystems
