module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

theorem prependN_coneN (σ ρ : Strn A) : prependN σ (coneN ρ) = coneN (σ ++ ρ) := by
  ext w
  simp only [mem_prependN, mem_coneN]
  constructor
  · rintro ⟨τ, hτ, rfl⟩; exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
