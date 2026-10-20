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

section ProdCase

variable (a b : ApproximableMap U U)

/-- **`J_× : 𝒰 → D_a × D_b`**, symmetric to `IProdComb`, via the projections `j_a`, `j_b`. -/
noncomputable def JProdComb : ApproximableMap U (prod (fixedNbhd a) (fixedNbhd b)) :=
  (prodMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jTimes

end ProdCase

end DomainTheory.NeighbourhoodSystems
