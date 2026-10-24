module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_19
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
/- concordance: source L1541 EXERCISE 3.20 sum and product functors -/
/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (uniqueness):
any `k` with `p₀ ∘ k = h₀` and `p₁ ∘ k = h₁` equals the pairing `⟨h₀, h₁⟩`. Hence `prod` with
`proj₀`, `proj₁` is the categorical product of `𝒟₀` and `𝒟₁`. -/
theorem paired_unique (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
    (k : ApproximableMap V₂ (prod V₀ V₁)) (hk₀ : (proj₀ V₀ V₁).comp k = h₀)
    (hk₁ : (proj₁ V₀ V₁).comp k = h₁) : k = paired h₀ h₁ := by
  rw [← hk₀, ← hk₁, paired_proj]

/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (existence):
`p₀ ∘ ⟨h₀, h₁⟩ = h₀` and `p₁ ∘ ⟨h₀, h₁⟩ = h₁` (these are Proposition 3.4(i)). -/
theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves composition:
`(f' ∘ f) × (g' ∘ g) = (f' × g') ∘ (f × g)`. -/
theorem prodMap_comp {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]
end
end DomainTheory.NeighbourhoodSystems
end
