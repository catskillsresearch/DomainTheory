module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JArrowComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ArrowCase

variable (a b : ApproximableMap U U)

theorem JArrowComb_comp_IArrowComb :
    (JArrowComb a b).comp (IArrowComb a b) =
      idMap (funSpace (fixedNbhd a) (fixedNbhd b)) := by
  unfold JArrowComb IArrowComb
  rw [comp_assoc, ← comp_assoc jArrow iArrow (expMap _ _), jArrow_comp_iArrow, idMap_comp,
    ← expMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    expMap_id]

end ArrowCase

end DomainTheory.NeighbourhoodSystems
