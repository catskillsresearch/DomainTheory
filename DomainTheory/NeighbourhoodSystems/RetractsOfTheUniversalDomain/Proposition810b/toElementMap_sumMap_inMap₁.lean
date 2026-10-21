/-ai
The sum map of f and g sends the right inclusion of an element to the right inclusion of its image under g.

The image reaches the right copy, because the right inclusion does and the sum map preserves right reach, so the right round trip recovers the image from its right projection. The right projection of the image equals the right projection composed with the sum map composed with the right inclusion, by the two composition rules for element maps, and that composite equals g.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_reaches_right

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

theorem toElementMap_sumMap_inMap₁ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (w : V1.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap (g.toElementMap w) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) with hz
  have hRz : ∃ Y', V1'.mem Y' ∧ z.mem (inj₁ Y') :=
    sumMap_reaches_right (inMap₁_toElementMap_reaches_right w)
  rw [← inMap₁_outMap₁_eq_of_right hRz]
  congr 1
  have heq : (outMap₁ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₁ (h₀ := h0) (h₁ := h1))) = g :=
    outMap₁_comp_sumMap_comp_inMap₁ f g
  calc (outMap₁ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₁ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₁ (h₀ := h0) (h₁ := h1)))).toElementMap w := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = g.toElementMap w := by rw [heq]

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
