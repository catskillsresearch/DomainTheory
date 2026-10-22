module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem coneN_subset_coneN {σ τ : Strn A} : coneN σ ⊆ coneN τ ↔ τ <+: σ := by
  constructor
  · intro h; exact h (show σ ∈ coneN σ from List.prefix_rfl)
  · intro hτσ w hw; exact hτσ.trans hw

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
