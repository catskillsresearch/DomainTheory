/-ai
If a sum element reaches the left copy, then its image under the sum map also reaches the left copy.

From a left neighbourhood of the element, monotonicity of the left map, applied to the master relation and the inclusion of that neighbourhood in the master, shows that the left map relates the neighbourhood to the master of the target left system. The master of that system, the left injection of the source neighbourhood, and the three left clauses of the sum-map relation witness that the image meets the left injection of the target master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

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

/-- If `y` reaches the left copy, `(sumMap f g)(y)` also reaches the left copy. -/
theorem sumMap_reaches_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    ∃ X', V0'.mem X' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₀ X') := by
  obtain ⟨X, hX, hXy⟩ := hL
  have hf : f.rel X V0'.master :=
    f.mono f.master_rel (V0.sub_master hX) subset_rfl hX V0'.master_mem
  exact ⟨V0'.master, V0'.master_mem, inj₀ X, hXy,
    Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨V0'.master, V0'.master_mem, rfl⟩),
    Or.inr (Or.inl ⟨X, V0'.master, rfl, rfl, hf⟩)⟩

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
