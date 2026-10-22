module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.consistent_iff_bracket_interUpTo_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.consistent_iff_iInter_bracket_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.tokenSystem_complete
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.tokenSystem_isPositive
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.tokenSystem_toToken_bijective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_121.{u_1} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Function.Bijective (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toToken α V)) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Function.Bijective (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toToken α V))
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
    (@And.intro
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@And.intro
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x))
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_iff_bracket_interUpTo_nonempty
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_iff_iInter_bracket_nonempty)
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_complete)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_isPositive)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_toToken_bijective

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
