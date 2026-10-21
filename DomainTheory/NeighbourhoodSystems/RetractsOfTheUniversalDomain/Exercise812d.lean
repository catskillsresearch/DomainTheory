/-ai
The second presentation sends the code XPseqCode j to the same set as the code k if and only if the first presentation sends j to the same set as YPseqCode k. The index recorded on either side of the coded atom pair is always a neighbourhood of that side. Two codes have the same image in the first neighbourhood system if and only if their XPseqCode images coincide in the second. A code of the first presentation is contained in the image of YPseqCode j if and only if the image of its XPseqCode is contained in the code j of the second presentation. The image of YPseqCode i is contained in a code of the first presentation if and only if the corresponding code of the second presentation is contained in the image of XPseqCode at the other index. The code-level domain isomorphism is a computable map from the first presentation to the second. The inverse of the code-level domain isomorphism is a computable map from the second presentation to the first. The inverse of the code-level domain isomorphism, as an approximable map, is a left inverse of the forward map. The relation of the inverse of the code-level domain isomorphism, at a basic neighbourhood of index m in the second system and one of index n in the first, holds exactly when the second neighbourhood equals the basic neighbourhood of some Y-sequence code k and the first neighbourhood is contained in the basic neighbourhood of index k. The code-level pullback of the code-level pushforward of an element of the first system is that element. If a neighbourhood belongs to the code-level pullback of an element y, a second neighbourhood of the first system is genuine, and the first is contained in the second, then the second belongs to the pullback. The relation of the code-level domain isomorphism, at a basic neighbourhood of index n in the first system and one of index m in the second, holds exactly when the second neighbourhood equals the basic neighbourhood of some X-sequence code k and the first neighbourhood is contained in the basic neighbourhood of index k. The code-level pushforward of the code-level pullback of an element of the second system is that element. If a neighbourhood belongs to the code-level pushforward of an element x, a second neighbourhood of the second system is genuine, and the first is contained in the second, then the second belongs to the pushforward. The approximable map of the code-level domain isomorphism is a left inverse of the approximable map of its inverse, and their composite is the identity map of the second system.

The numbered name example_812_d is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_eq_Y_iff_X_eq_YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.X_eq_iff_XPseqCode_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.X_subset_YPseqCode_iff_XPseqCode_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode_subset_X_iff_Y_subset_XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.domainIsoCode812d_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.domainIsoCode812d_symm_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.invMap_comp_toMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code_rel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code_toD1Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code_up_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_rel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_toD0Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_up_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toMap_comp_invMap

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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                    @DomainTheory.NeighbourhoodSystems.IsComputableMap β α D₁ D₀ P₁ P₀
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
                      @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D₀ D₁ P₀ P₁
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
                              @DomainTheory.NeighbourhoodSystems.XPseqCode_eq_Y_iff_X_eq_YPseqCode
                              @DomainTheory.NeighbourhoodSystems.isomorphic_812d)
                            @DomainTheory.NeighbourhoodSystems.effectivelyIsomorphic_812d)
                          @DomainTheory.NeighbourhoodSystems.X_eq_iff_XPseqCode_eq)
                        @DomainTheory.NeighbourhoodSystems.X_subset_YPseqCode_iff_XPseqCode_subset_Y)
                      @DomainTheory.NeighbourhoodSystems.YPseqCode_subset_X_iff_Y_subset_XPseqCode)
                    @DomainTheory.NeighbourhoodSystems.domainIsoCode812d_isComputableMap)
                  @DomainTheory.NeighbourhoodSystems.domainIsoCode812d_symm_isComputableMap)
                @DomainTheory.NeighbourhoodSystems.invMap_comp_toMap)
              @DomainTheory.NeighbourhoodSystems.toD0Code_rel_iff)
            @DomainTheory.NeighbourhoodSystems.toD0Code_toD1Code)
          @DomainTheory.NeighbourhoodSystems.toD0Code_up_mem)
        @DomainTheory.NeighbourhoodSystems.toD1Code_rel_iff)
      @DomainTheory.NeighbourhoodSystems.toD1Code_toD0Code)
    @DomainTheory.NeighbourhoodSystems.toD1Code_up_mem)
  @DomainTheory.NeighbourhoodSystems.toMap_comp_invMap

end DomainTheory.NeighbourhoodSystems
