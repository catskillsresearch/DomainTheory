module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_paired

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(iii) (Scott 1981, PRG-19).** `h = ⟨p₀ ∘ h, p₁ ∘ h⟩`. -/
theorem paired_proj (h : ApproximableMap V₂ (prod V₀ V₁)) :
    paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, pair_fst_snd]

end DomainTheory.NeighbourhoodSystems
