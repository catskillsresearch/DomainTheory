/-ai
The neighbourhood presented by the negative bisection index depends only on the three presented sets.

The numbered name example_812_e is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.negIdxFromBisection_congr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ComputableBisection

set_option linter.unusedVariables false

theorem example_812_e.{u_1, u_2} : ∀ {α : Type u_1} {γ : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
  (hDiff : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α V P)
  {Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ W}
  (B : @DomainTheory.NeighbourhoodSystems.ComputableBisection γ W Q) {n n' k k' m m' : Nat},
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α V →
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α V →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α V →
        @Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P n)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P n') →
          @Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k') →
            @Eq (Set γ) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ W Q m)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ W Q m') →
              @Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ W Q
                  (@DomainTheory.NeighbourhoodSystems.ComputableBisection.negIdxFromBisection α γ V W P hDiff Q B n m
                    k))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ W Q
                  (@DomainTheory.NeighbourhoodSystems.ComputableBisection.negIdxFromBisection α γ V W P hDiff Q B n' m'
                    k')) :=
  @DomainTheory.NeighbourhoodSystems.ComputableBisection.negIdxFromBisection_congr

end DomainTheory.NeighbourhoodSystems.ComputableBisection
