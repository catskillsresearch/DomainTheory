module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.part_e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)


section Congr

variable {n n' k k' m m' : ℕ}


/-- **`negIdxFromBisection` is a well-defined function of sets**, the same argument as
`posIdxFromBisection_congr` with `B.right_congr` in place of `B.left_congr`. -/
theorem negIdxFromBisection_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hn : P.X n = P.X n') (hk : P.X k = P.X k')
    (hm : Q.X m = Q.X m') :
    Q.X (negIdxFromBisection P hDiff B n m k) = Q.X (negIdxFromBisection P hDiff B n' m' k') := by
  unfold negIdxFromBisection
  rw [emptyInterDec.congr P hpos hnomin hn hk, emptyDiffDec.congr P hDiff hdiffClosed hnomin hn hk]
  have hle1 := emptyInterDec.le_one P (Nat.pair n' k')
  have hle2 := emptyDiffDec.le_one P hDiff (Nat.pair n' k')
  have h1 : emptyInterDec P (Nat.pair n' k') = 0 ∨ emptyInterDec P (Nat.pair n' k') = 1 := by omega
  have h2 : emptyDiffDec P hDiff (Nat.pair n' k') = 0 ∨
      emptyDiffDec P hDiff (Nat.pair n' k') = 1 := by omega
  rcases h1 with h1 | h1
  · simp only [h1, selectFn_zero]
    rcases h2 with h2 | h2
    · simp only [h2, selectFn_zero]; exact B.right_congr m m' hm
    · simp only [h2, selectFn_one]; exact hm
  · simp only [h1, selectFn_one]; exact hm

end Congr
end ComputableBisection
end DomainTheory.NeighbourhoodSystems

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
