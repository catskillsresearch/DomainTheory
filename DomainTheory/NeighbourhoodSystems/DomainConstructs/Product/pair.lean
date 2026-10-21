/-ai
Definition 3.1 of Scott (1981, PRG-19) pairs elements x and y as the product element whose neighbourhoods are the product neighbourhoods of a neighbourhood of x and a neighbourhood of y. Such a product is a product neighbourhood. The intersection of two of them is the product of the intersections, and a larger product neighbourhood enlarges each component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Definition 3.1 (Scott 1981, PRG-19).** The element pairing `⟨x, y⟩ = {X ∪ Y ∣ X ∈ x, Y ∈ y}`. -/
def pair (x : V₀.Element) (y : V₁.Element) : (prod V₀ V₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prod_mem_prodNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

end DomainTheory.NeighbourhoodSystems
