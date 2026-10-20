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

/-- Every neighbourhood of `D_a := fixedNbhd a` is non-empty (inherited from `𝒰`). -/
theorem fixedNbhd_mem_nonempty (a : ApproximableMap U U) :
    ∀ X, (fixedNbhd a).mem X → X.Nonempty :=
  fun X hX => U_mem_nonempty X ((fixedNbhd_subsystem a).sub hX)

end DomainTheory.NeighbourhoodSystems
