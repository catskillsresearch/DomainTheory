/-ai
Theorem 3.5 of Scott (1981, PRG-19) is the equivalence between joint approximable maps out of a product and two-variable approximable maps. It sends a joint map to its two-variable restriction and a two-variable map to the induced joint map, with the two round trips as inverse operations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂_ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂_toMap₂

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Theorem 3.5 (Scott 1981, PRG-19).** The bijection between joint approximable mappings
`𝒟₀ × 𝒟₁ → 𝒟₂` and two-variable mappings `𝒟₀, 𝒟₁ → 𝒟₂`: a function of two arguments comes from
an approximable mapping iff it is separately approximable. -/
def map₂Equiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃ ApproximableMap₂ V₀ V₁ V₂ where
  toFun := toMap₂
  invFun := ofMap₂
  left_inv := ofMap₂_toMap₂
  right_inv := toMap₂_ofMap₂

end DomainTheory.NeighbourhoodSystems
