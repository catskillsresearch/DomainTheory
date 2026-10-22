module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem constMap_rel {b : V₁.Element} {X : Set α} {Y : Set β} :
    (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
