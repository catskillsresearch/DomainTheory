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

theorem paired_unique (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
    (k : ApproximableMap V₂ (prod V₀ V₁)) (hk₀ : (proj₀ V₀ V₁).comp k = h₀)
    (hk₁ : (proj₁ V₀ V₁).comp k = h₁) : k = paired h₀ h₁ := by
  rw [← hk₀, ← hk₁, paired_proj]

theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

theorem prodMap_comp {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]
end
end DomainTheory.NeighbourhoodSystems
end
