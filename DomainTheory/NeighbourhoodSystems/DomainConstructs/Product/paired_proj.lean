module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.map₂Equiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_split
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.pair_fst_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_preimage
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ext
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂_ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂_toMap₂
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
