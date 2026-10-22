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

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


/-- **Proposition 8.10(b) (Scott 1981, PRG-19), in full.** If `a, b : 𝒰 → 𝒰` are finitary
projections, then so are `a+b`, `a×b`, `a→b`, with `D_{a+b} ≅ D_a+D_b`, `D_{a×b} ≅ D_a×D_b`,
`D_{a→b} ≅ (D_a→D_b)`. -/
theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb⟩

end DomainTheory.NeighbourhoodSystems
