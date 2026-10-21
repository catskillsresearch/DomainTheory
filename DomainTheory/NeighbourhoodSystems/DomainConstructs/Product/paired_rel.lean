/-ai
The pairing of approximable maps f and g relates Z to a product neighbourhood P if and only if P is a product neighbourhood, f relates Z to the left preimage of P, and g relates Z to the right preimage of P.

The two sides are definitionally equal.
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem paired_rel {f : ApproximableMap V₂ V₀} {g : ApproximableMap V₂ V₁}
    {Z : Set γ} {P : Set (α ⊕ β)} :
    (paired f g).rel Z P ↔
      (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
