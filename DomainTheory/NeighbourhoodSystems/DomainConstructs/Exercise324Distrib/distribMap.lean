/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.prod_mem_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.24(iii) (Scott 1981, PRG-19).** The canonical *distribution* approximable map
`(𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂) → 𝒟₀ × (𝒟₁ + 𝒟₂)`, `inᵢ⟨x, u⟩ ↦ ⟨x, inᵢ u⟩`. (This direction always exists;
the reverse map / isomorphism does not, since the left side has an element `⟨x, ⊥⟩` for each `x`.) -/
def distribMap (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (hn₂ : ∀ Z, V₂.mem Z → Z.Nonempty) :
    ApproximableMap
      (sum (prod V₀ V₁) (prod V₀ V₂) (prod_mem_nonempty hn₀ hn₁) (prod_mem_nonempty hn₀ hn₂))
      (prod V₀ (sum V₁ V₂ hn₁ hn₂)) :=
  copair
    (paired (proj₀ V₀ V₁) ((inMap₀ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₁)))
    (paired (proj₀ V₀ V₂) ((inMap₁ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₂)))

end DomainTheory.NeighbourhoodSystems
