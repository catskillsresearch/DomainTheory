module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.inj_comp_proj_eq_self
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.prodMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.prodComb_eq
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

theorem IProdComb_comp_JProdComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (IProdComb a b).comp (JProdComb a b) = prodComb a b := by
  unfold IProdComb JProdComb
  rw [comp_assoc, ← comp_assoc (prodMap _ _) (prodMap _ _) jTimes, ← prodMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc, prodComb_eq, comp_assoc]

end ProdCase

end DomainTheory.NeighbourhoodSystems
