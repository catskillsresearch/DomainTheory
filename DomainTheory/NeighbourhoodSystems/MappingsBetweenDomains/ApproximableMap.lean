module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α β γ δ : Type*}

structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where

  rel : Set α → Set β → Prop

  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X

  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y

  master_rel : rel V₀.master V₁.master

  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')

  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
