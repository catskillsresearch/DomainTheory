/-ai
If two self-maps of the universal domain are finitary projections, then so are their sum, their product, and their arrow. The fixed elements of each combinator are order-isomorphic to the corresponding combinator of the fixed neighbourhoods.

Pair the three finitary-projection theorems for the sum, the product, and the arrow.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_arrowComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}














/-- **Proposition 8.10(b) (Scott 1981, PRG-19), in full.** If `a, b : 𝒰 → 𝒰` are finitary
projections, then so are `a+b`, `a×b`, `a→b`, with `D_{a+b} ≅ D_a+D_b`, `D_{a×b} ≅ D_a×D_b`,
`D_{a→b} ≅ (D_a→D_b)`. -/
theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
      IsFinitaryProjection (arrowComb a b) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb⟩

end DomainTheory.NeighbourhoodSystems
