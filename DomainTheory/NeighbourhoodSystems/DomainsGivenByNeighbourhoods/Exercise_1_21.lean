module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem_1_10
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem consistent_iff_bracket_interUpTo_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty := by
  rw [V.consistent_iff_interUpTo_mem X hX]
  exact V.bracket_nonempty_iff.symm

theorem consistent_iff_iInter_bracket_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ ∃ x : V.Element, ∀ i, i < n → x ∈ V.bracket (X i) := by
  rw [V.consistent_iff_bracket_interUpTo_nonempty X hX]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i hi => x.up_mem hx (hX i hi) (V.interUpTo_subset X hi)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.mem_interUpTo X (fun i hi => hx i hi)⟩

theorem tokenSystem_complete : V.tokenSystem.IsComplete := by
  intro y
  refine ⟨V.ofToken y, ?_, ?_⟩
  · rintro S ⟨W, hW, rfl⟩
    constructor
    · intro hyW; exact ⟨hW, hyW⟩
    · rintro ⟨_, hyW⟩; exact hyW
  · intro b hb
    apply Element.ext
    intro W
    by_cases hW : V.mem W
    · have hb' := hb (V.bracket W) ⟨W, hW, rfl⟩
      constructor
      · intro hbW; exact ⟨hW, hb'.mpr hbW⟩
      · intro hxW; exact hb'.mp hxW.2
    · constructor
      · intro hbW; exact absurd (b.sub hbW) hW
      · intro hxW; exact absurd ((V.ofToken y).sub hxW) hW

theorem tokenSystem_isPositive : V.tokenSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.bracket_inter hX hY]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨V.principal hW, V.principal_mem_bracket hW⟩
  · rintro ⟨x, hx⟩
    exact ⟨X ∩ Y, x.sub hx, rfl⟩

theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

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
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end
