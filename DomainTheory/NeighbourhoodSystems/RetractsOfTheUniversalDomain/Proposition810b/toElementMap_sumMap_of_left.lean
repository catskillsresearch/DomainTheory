/-ai
If a sum element reaches the left copy, the sum map sends it to the left inclusion of f applied to its left projection.

The left round trip rewrites the element as the left inclusion of its left projection, and the inclusion formula for the sum map gives the result.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_inMap₀

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

theorem toElementMap_sumMap_of_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap
        (f.toElementMap ((outMap₀ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₀_outMap₀_eq_of_left hL]
  exact toElementMap_sumMap_inMap₀ f g _

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
