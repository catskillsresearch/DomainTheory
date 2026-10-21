/-ai
If two approximable maps on the universal domain are projections, then so are their sum, product, and arrow combinators. If the two maps are finitary projections, then so are those three combinators.

The first claim is the preservation of projections by the three combinators. The second is the preservation of finitary projections by the three combinators.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise818.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.18 (Scott 1981, PRG-19), in full: Proposition 8.10, both halves, all three
combinators.** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, `a→b`
(`isProjection_combinators`); if moreover `a, b` are finitary, then so are `a+b`, `a×b`, `a→b`
(`finitaryProjection_combinators`) — and (packaged inside `IsFinitaryProjection`'s `IsFinitary`
witness) the fixed-point set of each is isomorphic to the corresponding construct applied to `D_a`,
`D_b` (`sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso` in `Proposition810b.lean`).
No case of Proposition 8.10 is left unestablished. -/
theorem exercise_8_18 {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (IsFinitaryProjection a → IsFinitaryProjection b →
        IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
          IsFinitaryProjection (arrowComb a b)) :=
  ⟨isProjection_combinators ha hb, fun hfa hfb => finitaryProjection_combinators hfa hfb⟩

end DomainTheory.NeighbourhoodSystems
