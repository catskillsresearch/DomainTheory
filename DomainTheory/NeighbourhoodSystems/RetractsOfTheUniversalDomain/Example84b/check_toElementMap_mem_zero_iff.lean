module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- `check(x) ∋ {0} ↔ x ≠ ⊥`: the clean, non-set-theoretic form of `mem_toElementMap_check`. -/
theorem check_toElementMap_mem_zero_iff {x : D.Element} :
    (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
  rw [mem_toElementMap_check]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h fin2_zero_ne_zero_one
    · exact h
  · intro h; exact ⟨O_mem_zero, Or.inr h⟩

end DomainTheory.NeighbourhoodSystems
