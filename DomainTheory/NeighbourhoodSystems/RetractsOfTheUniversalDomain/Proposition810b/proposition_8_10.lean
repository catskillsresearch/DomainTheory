/-ai
Scott's Proposition 8.10 says that if a and b are finitary projections on the universal domain, then so are their sum, product, and arrow combinations, and the elements of the sum, the product, and the function space of their fixed neighbourhood systems are order-isomorphic to the fixed-point sets of those combinations.

The conjunction assembles the three finitary-projection results for the sum, the product, and the arrow combination with the three element isomorphisms of those combinations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_arrowComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Proposition 8.10 (Scott 1981, PRG-19).** If `a, b : 𝒰 → 𝒰` are finitary projections, then
so are `a+b`, `a×b`, and `a→b`, and `D_{a+b} ≅ D_a + D_b`, `D_{a×b} ≅ D_a × D_b`,
`D_{a→b} ≅ (D_a → D_b)`, where `D_a = fixedNbhd a` and `D_b = fixedNbhd b`. -/
theorem proposition_8_10 {a b : ApproximableMap U U}
    (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
      IsFinitaryProjection (arrowComb a b) ∧
      Nonempty
        ((sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
            (fixedNbhd_mem_nonempty b)).Element ≃o
          {y : U.Element // (sumComb a b).toElementMap y = y}) ∧
      Nonempty
        ((prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (prodComb a b).toElementMap y = y}) ∧
      Nonempty
        ((funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (arrowComb a b).toElementMap y = y}) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb, ⟨sumComb_elementIso a b ha hb⟩,
    ⟨prodComb_elementIso a b ha hb⟩, ⟨arrowComb_elementIso a b ha hb⟩⟩

end DomainTheory.NeighbourhoodSystems
