/-ai
For every element of a separated sum, the conditional applied to the discriminator of that element and the two injected projections returns the element.

Compare neighbourhoods, rewriting by the elementwise criterion for the conditional and the two membership criteria for the discriminator. A left alternative rewrites by the left round-trip identity, a right alternative by the right round-trip identity, and a master alternative is the master membership. Conversely, the trichotomy splits the element into a left element, a right element, or an element for which every neighbourhood is the master, and these are the three alternatives of the criterion, the first two rewritten by the round-trip identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.which_mem_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.which_mem_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inMapu2080_outMapu2080_eq_of_left
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inMapu2081_outMapu2081_eq_of_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.sum_element_trichotomy

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
















/-- **Exercise 3.26 (Scott 1981, PRG-19).** Scott's identity for the discriminator:
`cond(which x, in₀(out₀ x), in₁(out₁ x)) = x` for every `x ∈ |D₀ + D₁|`. -/
theorem cond_which (x : (sum V₀ V₁ h₀ h₁).Element) :
    (cond (sum V₀ V₁ h₀ h₁)).toElementMap
        (pair ((whichMap V₀ V₁ h₀ h₁).toElementMap x)
          (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x))
                ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x)))) = x := by
  apply Element.ext
  intro Z
  rw [cond_toElementMap_mem, which_mem_zero, which_mem_one]
  constructor
  · rintro (⟨hL, ha⟩ | ⟨hR, hb⟩ | rfl)
    · rwa [inMap₀_outMap₀_eq_of_left hL] at ha
    · rwa [inMap₁_outMap₁_eq_of_right hR] at hb
    · exact x.master_mem
  · intro hxZ
    rcases sum_element_trichotomy x with hL | hR | hN
    · exact Or.inl ⟨hL, by rw [inMap₀_outMap₀_eq_of_left hL]; exact hxZ⟩
    · exact Or.inr (Or.inl ⟨hR, by rw [inMap₁_outMap₁_eq_of_right hR]; exact hxZ⟩)
    · exact Or.inr (Or.inr (hN Z hxZ))

end DomainTheory.NeighbourhoodSystems.Exercise326
