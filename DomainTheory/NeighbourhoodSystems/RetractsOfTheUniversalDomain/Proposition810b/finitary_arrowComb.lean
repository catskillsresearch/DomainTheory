/-ai
If a and b are finitary projections, then their arrow combination is finitary, with witnessing domain the function space of the fixed neighbourhood systems of a and b.

The criterion that an endomap equal to a projection pair is finitary is applied to the arrow injection and the arrow projection. The projection composed with the injection is the identity, and reversing the identity for the injection composed with the projection matches the arrow combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.isFinitary_of_projectionPair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


section ArrowCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `→`-case.** `a, b` finitary projections `⟹` `a → b` is finitary, with
witnessing domain `D_a → D_b`. -/
theorem finitary_arrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

end ArrowCase
end DomainTheory.NeighbourhoodSystems
