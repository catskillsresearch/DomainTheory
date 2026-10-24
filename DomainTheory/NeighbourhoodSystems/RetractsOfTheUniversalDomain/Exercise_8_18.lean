module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
/- concordance: source L5177 EXERCISE 8.18 missing proofs of 8.10 -/
/-- **Exercise 8.18 (Scott 1981, PRG-19), in full: Proposition 8.10, both halves, all three
combinators.** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, `a→b`
(`isProjection_combinators`); if moreover `a, b` are finitary, then so are `a+b`, `a×b`, `a→b`
(`finitaryProjection_combinators`) — and (packaged inside `FinitaryProjection`'s `IsFinitary`
witness) the fixed-point set of each is isomorphic to the corresponding construct applied to `D_a`,
`D_b` (`sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso` in `Proposition810b.lean`).
No case of Proposition 8.10 is left unestablished. -/
theorem exercise_8_18 {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (FinitaryProjection a → FinitaryProjection b →
        FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
          FinitaryProjection (arrowComb a b)) :=
  ⟨isProjection_combinators ha hb, fun hfa hfb => finitaryProjection_combinators hfa hfb⟩
end

section
set_option linter.unusedVariables false

theorem example_818 : ∀
  {a b :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U},
  @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
      And
        (And
          (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.sumComb a b))
          (And
            (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.prodComb a b))
            (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b))
              (And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))) :=
  @DomainTheory.NeighbourhoodSystems.exercise_8_18
end

end DomainTheory.NeighbourhoodSystems
end

section
end
