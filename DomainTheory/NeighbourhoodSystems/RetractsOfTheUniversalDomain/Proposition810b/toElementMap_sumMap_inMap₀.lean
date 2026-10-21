/-ai
The sum map of f and g sends the left inclusion of an element to the left inclusion of its image under f.

The image reaches the left copy, because the left inclusion does and the sum map preserves left reach, so the left round trip recovers the image from its left projection. The left projection of the image equals the left projection composed with the sum map composed with the left inclusion, by the two composition rules for element maps, and that composite equals f.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_reaches_left

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

theorem toElementMap_sumMap_inMap₀ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (v : V0.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap (f.toElementMap v) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) with hz
  have hLz : ∃ X', V0'.mem X' ∧ z.mem (inj₀ X') :=
    sumMap_reaches_left (inMap₀_toElementMap_reaches_left v)
  rw [← inMap₀_outMap₀_eq_of_left hLz]
  congr 1
  have heq : (outMap₀ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₀ (h₀ := h0) (h₁ := h1))) = f :=
    outMap₀_comp_sumMap_comp_inMap₀ f g
  calc (outMap₀ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₀ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₀ (h₀ := h0) (h₁ := h1)))).toElementMap v := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = f.toElementMap v := by rw [heq]

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
