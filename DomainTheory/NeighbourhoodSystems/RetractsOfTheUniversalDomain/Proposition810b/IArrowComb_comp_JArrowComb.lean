/-ai
For finitary projections a and b, the arrow injection into the universal domain composed after the arrow extraction equals the arrow combinator of a and b.

Unfold both maps. Associativity, the composition law of the exponential, the identities that each subsystem injection after its projection is the finitary projection, the agreement of the exponential with the lambda combinator, and the composite form of the arrow combinator give the equality.
ai-/
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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ArrowCase

variable (a b : ApproximableMap U U)

theorem IArrowComb_comp_JArrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (IArrowComb a b).comp (JArrowComb a b) = arrowComb a b := by
  unfold IArrowComb JArrowComb
  rw [comp_assoc, ← comp_assoc (expMap _ _) (expMap _ _) jArrow, ← expMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, expMap_eq_lamComb, ← comp_assoc,
    arrowComb_eq, comp_assoc]

end ArrowCase

end DomainTheory.NeighbourhoodSystems
