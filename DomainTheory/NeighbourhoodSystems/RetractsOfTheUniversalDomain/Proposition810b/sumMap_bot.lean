/-ai
The sum map of two approximable maps sends the bottom element of the source sum to the bottom element of the target sum.

Extensionality of elements and the membership rule for the bottom reduce the claim to an equivalence for a neighbourhood of the target. If the image meets that neighbourhood, the witnessing source neighbourhood belongs to the bottom and hence is the master. The relating clause is then equality of the two masters, which is the goal, or a left injection of the master, which would put the token none in the master and in a left injection, or a right injection, which would put the token none in the master and in a right injection. If the target neighbourhood is the master, the master of the source, which belongs to the bottom and is a neighbourhood, together with the master of the target and equality of the masters, witnesses the relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

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

/-- `sumMap` sends the bottom element to the bottom element. -/
theorem sumMap_bot (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1') :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        (sum V0 V1 h0 h1).bot = (sum V0' V1' h0' h1').bot := by
  apply Element.ext
  intro Z
  rw [mem_bot]
  constructor
  · rintro ⟨W, hW, _, hZmem, hd⟩
    rw [mem_bot] at hW
    subst hW
    rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨Y, Y', hWY, -, -⟩
    · rfl
    · have hWX' : sumMaster V0 V1 = inj₀ X := hWX
      exact absurd (hWX' ▸ none_mem_sumMaster) none_mem_inj₀
    · have hWY' : sumMaster V0 V1 = inj₁ Y := hWY
      exact absurd (hWY' ▸ none_mem_sumMaster) none_mem_inj₁
  · rintro rfl
    exact ⟨sumMaster V0 V1, (sum V0 V1 h0 h1).mem_bot.mpr rfl, (sum V0 V1 h0 h1).master_mem,
      (sum V0' V1' h0' h1').master_mem, Or.inl rfl⟩

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
