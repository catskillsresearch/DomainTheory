/-ai
Proposition 3.4(iv) of Scott (1981, PRG-19) states that the value of the pairing of approximable maps f and g at w is the pairing of their values at w.

The two elements contain the same neighbourhoods. A neighbourhood of the paired value comes from one input neighbourhood related by both maps, and the preimage identity writes it as the product of those preimages. Conversely, two separate input neighbourhoods may be intersected; the intersection belongs to w, the product of the two codomains is a product neighbourhood, and monotonicity of each map along the intersection inclusions restores the two relations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(iv) (Scott 1981, PRG-19).** `⟨f, g⟩(w) = ⟨f(w), g(w)⟩`. -/
theorem toElementMap_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁)
    (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) := by
  apply Element.ext
  intro P
  constructor
  · rintro ⟨Z, hwZ, hP, hfZ, hgZ⟩
    exact ⟨Sum.inl ⁻¹' P, Sum.inr ⁻¹' P, ⟨Z, hwZ, hfZ⟩, ⟨Z, hwZ, hgZ⟩, prodNbhd_preimage hP⟩
  · rintro ⟨X, Y, ⟨Z₁, hwZ₁, hfZ₁⟩, ⟨Z₂, hwZ₂, hgZ₂⟩, rfl⟩
    refine ⟨Z₁ ∩ Z₂, w.inter_mem hwZ₁ hwZ₂, prod_mem_prodNbhd (f.rel_cod hfZ₁) (g.rel_cod hgZ₂),
      ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]
      exact f.mono hfZ₁ Set.inter_subset_left subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (f.rel_cod hfZ₁)
    · rw [inr_preimage_prodNbhd]
      exact g.mono hgZ₂ Set.inter_subset_right subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (g.rel_cod hgZ₂)

end DomainTheory.NeighbourhoodSystems
