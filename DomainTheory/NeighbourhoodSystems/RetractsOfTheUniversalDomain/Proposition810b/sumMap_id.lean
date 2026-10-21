/-ai
The sum map preserves identities: the sum of the two identity maps is the identity on the sum.

Extensionality of approximable maps reduces the equality to an element, and the identity acts as that element. The element reaches the left copy, the right copy, or neither. On the left, the left formula for the sum map, the identity on the left component, and the left round trip recover the element. On the right, the right formula, the identity on the right component, and the right round trip recover the element. If the element reaches neither copy, it is the bottom, and the sum map sends bottom to bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.reaches_neither_iff_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_right

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

/-- **`sumMap` preserves identities: `id + id = id`.** -/
theorem sumMap_id : sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0) (h₁' := h1)
    (idMap V0) (idMap V1) = idMap (sum V0 V1 h0 h1) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_idMap, inMap₀_outMap₀_eq_of_left hL]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_idMap, inMap₁_outMap₁_eq_of_right hR]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot]

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
