module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.inj_comp_proj_eq_self
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_eq_lamComb
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

theorem IArrowComb_comp_JArrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (IArrowComb a b).comp (JArrowComb a b) = arrowComb a b := by
  unfold IArrowComb JArrowComb
  rw [comp_assoc, ← comp_assoc (expMap _ _) (expMap _ _) jArrow, ← expMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, expMap_eq_lamComb, ← comp_assoc,
    arrowComb_eq, comp_assoc]

end ArrowCase

end DomainTheory.NeighbourhoodSystems
