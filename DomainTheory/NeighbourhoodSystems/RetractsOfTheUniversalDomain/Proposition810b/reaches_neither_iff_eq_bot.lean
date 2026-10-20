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

/-- A sum-element reaches "neither" copy iff it is the bottom element. -/
theorem reaches_neither_iff_eq_bot {y : (sum V0 V1 h0 h1).Element} :
    (∀ W, y.mem W → W = (sum V0 V1 h0 h1).master) ↔ y = (sum V0 V1 h0 h1).bot := by
  constructor
  · intro hN
    apply Element.ext
    intro W
    rw [mem_bot]
    exact ⟨hN W, fun h => h ▸ y.master_mem⟩
  · rintro rfl W hW
    rw [mem_bot] at hW
    exact hW

end SumMapLemmas

end DomainTheory.NeighbourhoodSystems
