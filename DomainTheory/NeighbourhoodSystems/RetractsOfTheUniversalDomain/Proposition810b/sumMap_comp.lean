/-ai
The sum map preserves composition: the sum of two composites equals the composite of the two sums.

Extensionality of approximable maps reduces the equality to the action on a sum element, and composition of element maps unfolds the composite. The element reaches the left copy, the right copy, or neither. On the left, the left formula for the sum map is used for the outer sum, for the inner sum, and again because the left inclusion reaches the left, and the identity given by the left projection composed with the left inclusion matches the two sides. On the right, the right formula and the identity given by the right projection composed with the right inclusion do the same. If the element reaches neither copy, it is the bottom, and the sum map sends bottom to bottom on both sides.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.reaches_neither_iff_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_right

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.inMapu2080_toElementMap_reaches_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.inMapu2081_toElementMap_reaches_right
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

/-- **`sumMap` preserves composition: `(f'∘f) + (g'∘g) = (f'+g') ∘ (f+g)`.** -/
theorem sumMap_comp (f' : ApproximableMap V0' V0'') (f : ApproximableMap V0 V0')
    (g' : ApproximableMap V1' V1'') (g : ApproximableMap V1 V1') :
    sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0'') (h₁' := h1'') (f'.comp f) (g'.comp g) =
      (sumMap (h₀ := h0') (h₁ := h1') (h₀' := h0'') (h₁' := h1'') f' g').comp
        (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_comp, toElementMap_sumMap_of_left hL,
      toElementMap_sumMap_of_left (inMap₀_toElementMap_reaches_left _),
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_comp, toElementMap_sumMap_of_right hR,
      toElementMap_sumMap_of_right (inMap₁_toElementMap_reaches_right _),
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot, sumMap_bot, sumMap_bot]

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
