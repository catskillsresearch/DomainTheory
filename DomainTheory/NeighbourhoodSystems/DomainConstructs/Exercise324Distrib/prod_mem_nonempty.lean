/-ai
A product neighbourhood is nonempty whenever neighbourhoods of the first factor are nonempty.

A product neighbourhood is a product of two neighbourhoods. The first of them contributes an element, and that element, tagged as a left summand, lies in the product neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A product neighbourhood over non-empty factors is non-empty. -/
theorem prod_mem_nonempty (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (_hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (W : Set (α ⊕ β)) (hW : (prod V₀ V₁).mem W) : W.Nonempty := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW
  obtain ⟨a, ha⟩ := hn₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

end DomainTheory.NeighbourhoodSystems
