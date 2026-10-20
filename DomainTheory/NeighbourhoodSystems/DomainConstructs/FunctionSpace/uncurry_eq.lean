module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.evalMap_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

















































variable {V₂ : NeighborhoodSystem γ}














/-- `uncurry` is the composition `eval ∘ ⟨h ∘ p₀, p₁⟩`. -/
theorem uncurry_eq (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    uncurry h = (evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, evalMap_apply]
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W₀, hwW₀, hW₀, hrel⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW₀
    rw [inl_preimage_prodNbhd] at hrel
    rw [inr_preimage_prodNbhd] at hrel
    obtain ⟨hwX, hwY⟩ := (prod_mem_split hX hY).mp hwW₀
    exact ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
  · rintro ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
    refine ⟨prodNbhd X Y, (prod_mem_split hX hY).mpr ⟨hwX, hwY⟩, prod_mem_prodNbhd hX hY, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact hrel

end DomainTheory.NeighbourhoodSystems
