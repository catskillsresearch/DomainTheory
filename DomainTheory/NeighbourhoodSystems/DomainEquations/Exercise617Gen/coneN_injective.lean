module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_subset_coneN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

theorem coneN_injective {σ τ : Strn A} (h : coneN σ = coneN τ) : σ = τ := by
  have h1 : τ <+: σ := coneN_subset_coneN.mp (le_of_eq h)
  have h2 : σ <+: τ := coneN_subset_coneN.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
