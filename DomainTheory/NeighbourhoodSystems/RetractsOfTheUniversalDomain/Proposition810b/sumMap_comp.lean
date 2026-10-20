module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.reaches_neither_iff_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_right

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

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
