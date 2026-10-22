module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

/-- **`i_a ∘ j_a = a`, for a finitary projection `a`.** Theorem 8.6's `sub_eq_self_of_isFinitaryProjection`,
restated via `retractionOfSubsystem`'s definition. -/
theorem inj_comp_proj_eq_self (ha : FinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

end DomainTheory.NeighbourhoodSystems
