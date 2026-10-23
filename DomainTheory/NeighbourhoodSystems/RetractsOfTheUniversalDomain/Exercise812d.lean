module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_7
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.domainIsoCode812d_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_d.{u_1, u_2} : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))))
        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
          (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
          (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
          (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
          (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
          (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
          (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
          (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
          (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
          (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
          (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
          (hX0 :
            @Eq (Set α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hY0 :
            @Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (n m : Nat),
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β D₀ D₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                  splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m))
            (∃ (k : Nat),
              And
                (@Eq (Set β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                      hSplitY hUnion1 k)))
                (@LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ k)))))
      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
        (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
        (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
        (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
        (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
        (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
        (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
        (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
        (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
        (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
        (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
        (hX0 :
          @Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hY0 :
          @Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
          (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
            hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0
            (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0 y))
          y))
    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
            @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                    @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                            (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀) {T1 T2 : Set β},
                            (∃ (n : Nat),
                                And
                                  (@Eq (Set β) T1
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                                        hSplitX splitY hSplitY hUnion1 n)))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))) →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ T2 →
                                @LE.le (Set β) (@Set.instLE β) T1 T2 →
                                  ∃ (n : Nat),
                                    And
                                      (@Eq (Set β) T2
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                          (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                            splitX hSplitX splitY hSplitY hUnion1 n)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))))
  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
    (hX0 :
      @Eq (Set α)
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
    (hY0 :
      @Eq (Set β)
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β D₁ D₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β D₁ D₀ D₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
            hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0 hY0))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
          (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
            (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β D₁)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))))
        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
          (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
          (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
          (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
          (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
          (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
          (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
          (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
          (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
          (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
          (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
          (hX0 :
            @Eq (Set α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hY0 :
            @Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (n m : Nat),
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β D₀ D₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                  splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m))
            (∃ (k : Nat),
              And
                (@Eq (Set β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                      hSplitY hUnion1 k)))
                (@LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ k)))))
      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
        (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
        (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
        (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
        (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
        (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
        (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
        (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
        (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
        (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
        (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
        (hX0 :
          @Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hY0 :
          @Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
          (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
            hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0
            (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0 y))
          y))
    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
            @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                    @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                            (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀) {T1 T2 : Set β},
                            (∃ (n : Nat),
                                And
                                  (@Eq (Set β) T1
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                                        hSplitX splitY hSplitY hUnion1 n)))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))) →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ T2 →
                                @LE.le (Set β) (@Set.instLE β) T1 T2 →
                                  ∃ (n : Nat),
                                    And
                                      (@Eq (Set β) T2
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                          (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                            splitX hSplitX splitY hSplitY hUnion1 n)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))))
  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
    (hX0 :
      @Eq (Set α)
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
    (hY0 :
      @Eq (Set β)
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β D₁ D₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β D₁ D₀ D₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
            hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0 hY0))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
          (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
            (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β D₁))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))))
        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
          (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
          (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
          (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
          (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
          (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
          (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
          (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
          (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
          (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
          (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
          (hX0 :
            @Eq (Set α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hY0 :
            @Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (n m : Nat),
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β D₀ D₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                  splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m))
            (∃ (k : Nat),
              And
                (@Eq (Set β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                      hSplitY hUnion1 k)))
                (@LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ k)))))
      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
        (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
        (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
        (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
        (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
        (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
        (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
        (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
        (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
        (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
        (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
        (hX0 :
          @Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hY0 :
          @Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
          (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
            hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0
            (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0 y))
          y))
    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
            @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                    @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                            (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀) {T1 T2 : Set β},
                            (∃ (n : Nat),
                                And
                                  (@Eq (Set β) T1
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                                        hSplitX splitY hSplitY hUnion1 n)))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))) →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ T2 →
                                @LE.le (Set β) (@Set.instLE β) T1 T2 →
                                  ∃ (n : Nat),
                                    And
                                      (@Eq (Set β) T2
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                          (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                            splitX hSplitX splitY hSplitY hUnion1 n)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α D₀ x
                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))))
        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
          (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
          (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
          (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
          (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
          (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
          (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
          (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
          (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
          (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
          (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
          (hX0 :
            @Eq (Set α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hY0 :
            @Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (n m : Nat),
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β D₀ D₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                  splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m))
            (∃ (k : Nat),
              And
                (@Eq (Set β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                      hSplitY hUnion1 k)))
                (@LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ k)))))
      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
        (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
        (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
        (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
        (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
        (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
        (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
        (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
        (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
        (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
        (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
        (hX0 :
          @Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
        (hY0 :
          @Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
          (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
            hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
            (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
            (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1
            hX0
            (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
              (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
              (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
              hUnion1 hX0 hY0 y))
          y)
      (@And.intro
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))))
        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
          (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
          (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
          (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
          (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
          (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
          (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
          (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
          (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
          (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
          (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
          (hX0 :
            @Eq (Set α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
          (hY0 :
            @Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
          (n m : Nat),
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β D₀ D₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                  splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m))
            (∃ (k : Nat),
              And
                (@Eq (Set β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                      hSplitY hUnion1 k)))
                (@LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ k))))
        (@And.intro
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x))
          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                                  {S1 S2 : Set α},
                                  (∃ (n : Nat),
                                      And
                                        (@Eq (Set α) S1
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1
                                              splitX hSplitX splitY hSplitY hUnion0 n)))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n))) →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S2 →
                                      @LE.le (Set α) (@Set.instLE α) S1 S2 →
                                        ∃ (n : Nat),
                                          And
                                            (@Eq (Set α) S2
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                  hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)))
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β D₁ y
                                              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ n)))
          (@And.intro
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k)))))
            (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
              (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
              (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
              (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
              (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
              (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
              (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
              (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
              (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
              (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
              (hX0 :
                @Eq (Set α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
              (hY0 :
                @Eq (Set β)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                (@DomainTheory.NeighbourhoodSystems.toD0Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                  hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                  (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                  (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                  hUnion1 hX0 hY0
                  (@DomainTheory.NeighbourhoodSystems.toD1Code α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                    hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y) (fun {X : Set α} => @hD₀nomin X)
                    (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos (fun {X Y : Set β} => @hD₁diff X Y)
                    (fun {X : Set β} => @hD₁nomin X) (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0
                    hUnion1 hX0 x))
                x)
            (@And.intro
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀)))
              (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                (hX0 :
                  @Eq (Set α)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                (hY0 :
                  @Eq (Set β)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                (m n : Nat),
                Iff
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel β α D₁ D₀
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                      (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n))
                  (∃ (k : Nat),
                    And
                      (@Eq (Set α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀ n)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX hSplitX
                            splitY hSplitY hUnion0 k)))
                      (@LE.le (Set β) (@Set.instLE β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ m)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁ k))))
              (@And.intro
                (And
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))))
                (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                  (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                  (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                  (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                  (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                  (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                  (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                  (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                  (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                  (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                  (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                  (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                  (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                  (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                  (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                  (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                  (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                  (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                  (hX0 :
                    @Eq (Set α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                  (hY0 :
                    @Eq (Set β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D₀ D₀)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D₀ D₁ D₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                        (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                          hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                          (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                          (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                          (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D₀))
                (@And.intro
                  (And
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                    (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                    (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                    (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                    (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                    (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                    (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                    (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                    (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                    (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                    (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                    (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                    (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                    (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                    (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                    (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                    (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                    (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                    (hX0 :
                      @Eq (Set α)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                    (hY0 :
                      @Eq (Set β)
                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β α D₁ D₀ P₁ P₀
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso β α D₁ D₀
                        (@OrderIso.symm (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D₀)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D₀)))
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β D₁)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β D₁)))
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0))))
                  (@And.intro
                    (And
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                    (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                      (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                      (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                      (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                      (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                      (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                      (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY)
                      (hD₀pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀)
                      (hD₀diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀)
                      (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀)
                      (hxSplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX)
                      (hD₁pos : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁)
                      (hD₁diff : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁)
                      (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (hySplit : @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY)
                      (hD₀mne : @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hD₁mne : @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
                      (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                      (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                      (hX0 :
                        @Eq (Set α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
                      (hY0 :
                        @Eq (Set β)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α β D₀ D₁ P₀ P₁
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β D₀ D₁
                          (@DomainTheory.NeighbourhoodSystems.domainIsoCode812d α β D₀ D₁ P₀ P₁ hDiff0 hDiff1 splitX
                            hSplitX splitY hSplitY hD₀pos (fun {X Y : Set α} => @hD₀diff X Y)
                            (fun {X : Set α} => @hD₀nomin X) (fun {A : Set α} {B : Set β} => @hxSplit A B) hD₁pos
                            (fun {X Y : Set β} => @hD₁diff X Y) (fun {X : Set β} => @hD₁nomin X)
                            (fun {A : Set β} {B : Set α} => @hySplit A B) hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)))
                    (@And.intro
                      (And
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j))))
                      (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                        {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                        (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                        (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                        (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                        (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                        (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                        (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                              @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                        @Set.Nonempty α
                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                          @Set.Nonempty β
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                            ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                              (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                              (i j : Nat),
                                              Iff
                                                (@LE.le (Set α) (@Set.instLE α)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                    j))
                                                (@LE.le (Set β) (@Set.instLE β)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    i)
                                                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                    (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁ hDiff0
                                                      hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))))
                      (@And.intro
                        (And
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j)))))
                        (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                          {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                          (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                          (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                          (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                          (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                          (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                          (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                          @Set.Nonempty α
                                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                            @Set.Nonempty β
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                              ∀ (hUnion0 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                (hUnion1 : @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                (i j : Nat),
                                                Iff
                                                  (@LE.le (Set α) (@Set.instLE α)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      i)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀ P₀
                                                      (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j)))
                                                  (@LE.le (Set β) (@Set.instLE β)
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                        hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁ P₁
                                                      j)))
                        (@And.intro
                          (And
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁))
                          (∀ {α : Type u_1} {β : Type u_2} {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                            {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                            (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                            (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                            (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                            (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                            (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                            (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                            (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                            (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                            @Set.Nonempty α
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Set.Nonempty β
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                ∀
                                                  (hUnion0 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                  (hUnion1 :
                                                    @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                  (i j : Nat),
                                                  Iff
                                                    (@Eq (Set α)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ i)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α D₀
                                                        P₀ j))
                                                    (@Eq (Set β)
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i))
                                                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β D₁
                                                        P₁
                                                        (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀ P₁
                                                          hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))))
                          (@And.intro
                            (And
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
                            (∀ {α : Type u_1} {β : Type u_2}
                              {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                              {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                              (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                              (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                              (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                              (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                              (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                              (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                              (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                              (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                              @Set.Nonempty α
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                                @Set.Nonempty β
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                      D₁) →
                                                  ∀
                                                    (hUnion0 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                    (hUnion1 :
                                                      @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                    @Eq (Set α)
                                                        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                          D₀ P₀
                                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                          D₀) →
                                                      @Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            β D₁) →
                                                        @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic
                                                          α β D₀ D₁ P₀ P₁)
                            (@And.intro
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁)
                                                      (j k : Nat),
                                                      Iff
                                                        (@Eq (Set β)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁
                                                            (@DomainTheory.NeighbourhoodSystems.XPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j))
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β
                                                            D₁ P₁ k))
                                                        (@Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀ j)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@DomainTheory.NeighbourhoodSystems.YPseqCode α β D₀ D₁ P₀
                                                              P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
                                                              k))))
                              (∀ {α : Type u_1} {β : Type u_2}
                                {D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                                {D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D₀)
                                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β D₁)
                                (hDiff0 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff α D₀ P₀)
                                (hDiff1 : @DomainTheory.NeighbourhoodSystems.IsComputableDiff β D₁ P₁)
                                (splitX : Set α → Set β → Set α → Prod (Set β) (Set β))
                                (hSplitX : @DomainTheory.NeighbourhoodSystems.IsComputableSplit α β D₀ D₁ P₀ P₁ splitX)
                                (splitY : Set β → Set α → Set β → Prod (Set α) (Set α))
                                (hSplitY : @DomainTheory.NeighbourhoodSystems.IsComputableSplit β α D₁ D₀ P₁ P₀ splitY),
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                                      @DomainTheory.NeighbourhoodSystems.SplitSpec' α β D₁ splitX →
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                                              @DomainTheory.NeighbourhoodSystems.SplitSpec' β α D₀ splitY →
                                                @Set.Nonempty α
                                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α
                                                      D₀) →
                                                  @Set.Nonempty β
                                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β
                                                        D₁) →
                                                    ∀
                                                      (hUnion0 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion α D₀ P₀)
                                                      (hUnion1 :
                                                        @DomainTheory.NeighbourhoodSystems.IsComputableUnion β D₁ P₁),
                                                      @Eq (Set α)
                                                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α
                                                            D₀ P₀
                                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                            α D₀) →
                                                        @Eq (Set β)
                                                            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                                                              β D₁ P₁
                                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master
                                                              β D₁) →
                                                          @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁)
                              @DomainTheory.NeighbourhoodSystems.XPseqCode.eq_Y_iff_X_eq_YPseqCode
                              @DomainTheory.NeighbourhoodSystems.isomorphic_812d)
                            @DomainTheory.NeighbourhoodSystems.effectivelyIsomorphic_812d)
                          @DomainTheory.NeighbourhoodSystems.X_eq_iff_XPseqCode_eq)
                        @DomainTheory.NeighbourhoodSystems.X_subset_YPseqCode_iff_XPseqCode_subset_Y)
                      @DomainTheory.NeighbourhoodSystems.YPseqCode.subset_X_iff_Y_subset_XPseqCode)
                    @DomainTheory.NeighbourhoodSystems.domainIsoCode812d.isComputableMap)
                  @DomainTheory.NeighbourhoodSystems.domainIsoCode812d.symm_isComputableMap)
                @DomainTheory.NeighbourhoodSystems.invMap_comp_toMap)
              @DomainTheory.NeighbourhoodSystems.toD0Code.rel_iff)
            @DomainTheory.NeighbourhoodSystems.toD0Code.toD1Code)
          @DomainTheory.NeighbourhoodSystems.toD0Code.up_mem)
        @DomainTheory.NeighbourhoodSystems.toD1Code.rel_iff)
      @DomainTheory.NeighbourhoodSystems.toD1Code.toD0Code)
    @DomainTheory.NeighbourhoodSystems.toD1Code.up_mem)
  @DomainTheory.NeighbourhoodSystems.toMap_comp_invMap

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **A union of two genuine `U`-neighbourhoods is again genuine, unconditionally** — no
`NoMinimal`/`DiffClosed` detour needed for `U` specifically: `U.mem`'s three conjuncts (presentable,
non-empty, `⊆ [0,1)`) each transfer directly across `∪` (presentability via list `++`; non-emptiness
since one side alone is already non-empty; the subset bound is monotone in `∪`). -/
theorem U_union_UX_mem (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨⟨L1, hL1⟩, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨⟨L2, hL2⟩, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨L1 ++ L2, by rw [presentedIntervals_append, hL1, hL2]⟩,
    hne1.mono Set.subset_union_left, Set.union_subset hsub1 hsub2⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The **raw** `(level, mask)` code for `VX n ∪ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myLor`. Mirrors `VinterRaw`
verbatim, substituting `myLor` for `myLand`. -/
def VunionRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLor
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `decodeQPairList` commutes with `appendListCode` (it is just `decodeList` followed by a fixed
`map`, and `List.map` commutes with `++`). -/
theorem decodeQPairList_appendListCode (c1 c2 : ℕ) :
    decodeQPairList (appendListCode c1 c2) = decodeQPairList c1 ++ decodeQPairList c2 := by
  unfold decodeQPairList
  rw [appendListCode_eq, List.map_append]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The low-bit XOR `(x ^^^ y) % 2`, in arithmetic `{0,1}`-valued form: the sum of the low bits,
mod `2`. -/
def lowXor (x y : ℕ) : ℕ := (x % 2 + y % 2) % 2

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `lowXor x y = (x ^^^ y) % 2`. -/
theorem lowXor_eq_mod (x y : ℕ) : lowXor x y = (x ^^^ y) % 2 := by
  unfold lowXor
  rw [Nat.xor_mod_two_eq]
  exact (Nat.add_mod x y 2).symm

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Packed iteration state `pair (pair curA curB) (pair weight acc)` for the bitwise-XOR fold. -/
def xorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2))

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The iterative bitwise XOR: iterate `xorStep` `a + b` times from the initial state, and read off
the accumulator. -/
def myXor (a b : ℕ) : ℕ :=
  (xorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `a` with `b`'s bits cleared: `a ^^^ (a &&& b)` (`testBit.xor_and_self`), computed via `myXor`
composed with the already-`Pass` `myLand`. -/
def myAndNot (a b : ℕ) : ℕ := myXor a (myLand a b)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The **raw** `(level, mask)` code for `VX n \ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myAndNot`. -/
def VdiffRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myAndNot
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- One recursion step for `Nat.xor` on the low bit: `x ^^^ y = 2 (x/2 ^^^ y/2) + lowXor x y`. -/
theorem xor_low_rec (x y : ℕ) : x ^^^ y = 2 * (x / 2 ^^^ y / 2) + lowXor x y := by
  have hdiv : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowXor_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ^^^ y) 2]
  rw [hdiv, hmod]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Invariant of the bitwise-XOR iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k ^^^ b/2^k) = a ^^^ b`. -/
theorem xorStep_iter_spec (a b : ℕ) : ∀ k,
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k ^^^ b / 2 ^ k) = a ^^^ b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have p11 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold xorStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold xorStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold xorStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowXor (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold xorStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, xor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Correctness of the iterative bitwise XOR.** `myXor a b = a ^^^ b`. -/
theorem myXor_eq_xor (a b : ℕ) : myXor a b = a ^^^ b := by
  unfold myXor
  obtain ⟨_, _, _, hAcc⟩ := xorStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myAndNot_eq (a b : ℕ) : myAndNot a b = a ^^^ (a &&& b) := by
  unfold myAndNot; rw [myXor_eq_xor, myLand_eq_land]

end DomainTheory.NeighbourhoodSystems
