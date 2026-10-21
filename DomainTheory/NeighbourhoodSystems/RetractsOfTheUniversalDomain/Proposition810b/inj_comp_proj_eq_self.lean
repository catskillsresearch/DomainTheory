/-ai
For a finitary projection, the injection of its fixed neighbourhood system composed with the projection equals the finitary projection.

The equality is the identity that a finitary projection equals that composition.
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

/-- **`i_a ∘ j_a = a`, for a finitary projection `a`.** Theorem 8.6's `sub_eq_self_of_isFinitaryProjection`,
restated via `retractionOfSubsystem`'s definition. -/
theorem inj_comp_proj_eq_self (ha : IsFinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

end DomainTheory.NeighbourhoodSystems
