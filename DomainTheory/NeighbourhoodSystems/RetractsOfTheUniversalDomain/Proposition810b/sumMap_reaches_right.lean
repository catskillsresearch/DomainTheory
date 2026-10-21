/-ai
If a sum element reaches the right copy, then its image under the sum map also reaches the right copy.

From a right neighbourhood of the element, monotonicity of the right map, applied to the master relation and the inclusion of that neighbourhood in the master, shows that the right map relates the neighbourhood to the master of the target right system. The master of that system, the right injection of the source neighbourhood, and the three right clauses of the sum-map relation witness that the image meets the right injection of the target master.
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

/-- If `y` reaches the right copy, `(sumMap f g)(y)` also reaches the right copy. -/
theorem sumMap_reaches_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    ∃ Y', V1'.mem Y' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₁ Y') := by
  obtain ⟨Y, hY, hYy⟩ := hR
  have hg : g.rel Y V1'.master :=
    g.mono g.master_rel (V1.sub_master hY) subset_rfl hY V1'.master_mem
  exact ⟨V1'.master, V1'.master_mem, inj₁ Y, hYy,
    Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨V1'.master, V1'.master_mem, rfl⟩),
    Or.inr (Or.inr ⟨Y, V1'.master, rfl, rfl, hg⟩)⟩

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
