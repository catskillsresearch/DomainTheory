module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryComb_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryComb_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryComb_rel_recDecidable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_716.{u_1, u_2, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
    (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gNa gNb gNc : Nat → Nat)
    (PA :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          V₂))
    (PB :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
    (Pc :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)),
    @Eq
        (Nat →
          Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          PA)
        (@DomainTheory.NeighbourhoodSystems.Xenum (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
          (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ gNa) →
      @Eq
          (Nat →
            Set
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PB)
          (@DomainTheory.NeighbourhoodSystems.Xenum α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀ Pc gNb) →
        @Eq (Nat → Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) Pc)
            (@DomainTheory.NeighbourhoodSystems.Xenum β γ V₁ V₂ P₁ P₂ gNc) →
          (∀ (c : Nat),
              Iff (@Eq Nat (gNa c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Set.Nonempty
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (@DomainTheory.NeighbourhoodSystems.stepFun (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                    (@DomainTheory.NeighbourhoodSystems.funListOf (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                      (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂
                      (Domain.Recursive.decodeList c))))) →
            (∀ (c : Nat),
                Iff (@Eq Nat (gNc c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                    (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                      (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂
                        (Domain.Recursive.decodeList c))))) →
              Nat.Primrec gNb →
                Nat.Primrec gNc →
                  Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        PA n)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        (@DomainTheory.NeighbourhoodSystems.funSpace α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        PB m)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
    (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gNa gNb gNc : Nat → Nat)
    (PA :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          V₂))
    (PB :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
    (Pc :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)),
    @Eq
        (Nat →
          Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          PA)
        (@DomainTheory.NeighbourhoodSystems.Xenum (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
          (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ gNa) →
      @Eq
          (Nat →
            Set
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PB)
          (@DomainTheory.NeighbourhoodSystems.Xenum α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀ Pc gNb) →
        @Eq (Nat → Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) Pc)
            (@DomainTheory.NeighbourhoodSystems.Xenum β γ V₁ V₂ P₁ P₂ gNc) →
          (∀ (c : Nat),
              Iff (@Eq Nat (gNa c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Set.Nonempty
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (@DomainTheory.NeighbourhoodSystems.stepFun (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                    (@DomainTheory.NeighbourhoodSystems.funListOf (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                      (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂
                      (Domain.Recursive.decodeList c))))) →
            (∀ (c : Nat),
                Iff (@Eq Nat (gNc c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                    (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                      (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂
                        (Domain.Recursive.decodeList c))))) →
              Nat.Primrec gNb →
                Nat.Primrec gNc →
                  Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        PA n)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        (@DomainTheory.NeighbourhoodSystems.funSpace α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        PB m))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))))
    @DomainTheory.NeighbourhoodSystems.curryComb_isComputable @DomainTheory.NeighbourhoodSystems.curryComb_rel)
  @DomainTheory.NeighbourhoodSystems.curryComb_rel_recDecidable

end DomainTheory.NeighbourhoodSystems
