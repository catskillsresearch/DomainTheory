module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_eq_Y_iff_X_eq_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_eq_iff_XPseq_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_subset_YPseq_iff_XPseq_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_subset_X_iff_Y_subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_inter_index_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_inter_index_Y

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_c.{u_1, u_2} : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j))))
        (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
              ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                    ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (X : Nat → Set α) (Y : Nat → Set β),
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                          @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                            @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                              ∀ (i j : Nat),
                                Iff
                                  (@LE.le (Set α) (@Set.instLE α)
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y i)
                                    (X j))
                                  (@LE.le (Set β) (@Set.instLE β) (Y i)
                                    (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y j))))
      (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
            ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                    (Y : Nat → Set β),
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                        @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                          @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                @Eq (Set α)
                                  (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                    (fun {X : Set β} => @hD₁nomin X) X Y
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀)))
    (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                  (Y : Nat → Set β),
                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          (∀ (S : Set α),
                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                (∃ (n : Nat), @Eq (Set α) S (X n))) →
                            ∀ {i j : Nat},
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀
                                  (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) →
                                ∃ (m : Nat),
                                  And (@Eq (Set α) (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) (X m))
                                    (@Eq (Set β)
                                      (@Inter.inter (Set β) (@Set.instInter β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y m))))
  (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
        ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
              ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                (Y : Nat → Set β),
                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                    @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                      @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                        (∀ (S : Set β),
                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                              (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                          ∀ {i j : Nat},
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁
                                (@Inter.inter (Set β) (@Set.instInter β) (Y i) (Y j)) →
                              ∃ (m : Nat),
                                And (@Eq (Set β) (@Inter.inter (Set β) (@Set.instInter β) (Y i) (Y j)) (Y m))
                                  (@Eq (Set α)
                                    (@Inter.inter (Set α) (@Set.instInter α)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y m))) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j))))
        (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
              ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                    ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (X : Nat → Set α) (Y : Nat → Set β),
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                          @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                            @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                              ∀ (i j : Nat),
                                Iff
                                  (@LE.le (Set α) (@Set.instLE α)
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y i)
                                    (X j))
                                  (@LE.le (Set β) (@Set.instLE β) (Y i)
                                    (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y j))))
      (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
            ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                    (Y : Nat → Set β),
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                        @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                          @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                @Eq (Set α)
                                  (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                    (fun {X : Set β} => @hD₁nomin X) X Y
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀)))
    (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                  (Y : Nat → Set β),
                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          (∀ (S : Set α),
                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                (∃ (n : Nat), @Eq (Set α) S (X n))) →
                            ∀ {i j : Nat},
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀
                                  (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) →
                                ∃ (m : Nat),
                                  And (@Eq (Set α) (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) (X m))
                                    (@Eq (Set β)
                                      (@Inter.inter (Set β) (@Set.instInter β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y m))))
  (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
        ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
              ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                (Y : Nat → Set β),
                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                    @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                      @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                        (∀ (S : Set β),
                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                              (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                          ∀ {i j : Nat},
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁
                                (@Inter.inter (Set β) (@Set.instInter β) (Y i) (Y j)) →
                              ∃ (m : Nat),
                                And (@Eq (Set β) (@Inter.inter (Set β) (@Set.instInter β) (Y i) (Y j)) (Y m))
                                  (@Eq (Set α)
                                    (@Inter.inter (Set α) (@Set.instInter α)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y m)))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j))))
        (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
              ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                    ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (X : Nat → Set α) (Y : Nat → Set β),
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                          @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                            @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                              ∀ (i j : Nat),
                                Iff
                                  (@LE.le (Set α) (@Set.instLE α)
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y i)
                                    (X j))
                                  (@LE.le (Set β) (@Set.instLE β) (Y i)
                                    (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y j))))
      (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
            ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                    (Y : Nat → Set β),
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                        @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                          @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                @Eq (Set α)
                                  (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                    (fun {X : Set β} => @hD₁nomin X) X Y
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀)))
    (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
          ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                  (Y : Nat → Set β),
                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                      @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                        @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                          (∀ (S : Set α),
                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                (∃ (n : Nat), @Eq (Set α) S (X n))) →
                            ∀ {i j : Nat},
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀
                                  (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) →
                                ∃ (m : Nat),
                                  And (@Eq (Set α) (@Inter.inter (Set α) (@Set.instInter α) (X i) (X j)) (X m))
                                    (@Eq (Set β)
                                      (@Inter.inter (Set β) (@Set.instInter β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y m)))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j))))
        (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
              ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                    ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (X : Nat → Set α) (Y : Nat → Set β),
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                          @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                            @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                              ∀ (i j : Nat),
                                Iff
                                  (@LE.le (Set α) (@Set.instLE α)
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y i)
                                    (X j))
                                  (@LE.le (Set β) (@Set.instLE β) (Y i)
                                    (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y j))))
      (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
            ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                  ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁) (X : Nat → Set α)
                    (Y : Nat → Set β),
                    (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                        @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                          @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                @Eq (Set α)
                                  (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                    (fun {X : Set β} => @hD₁nomin X) X Y
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀))
      (@And.intro
        (And
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j))))
        (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
              ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                    ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                      (X : Nat → Set α) (Y : Nat → Set β),
                      (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                          @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                            @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                              ∀ (i j : Nat),
                                Iff
                                  (@LE.le (Set α) (@Set.instLE α)
                                    (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y i)
                                    (X j))
                                  (@LE.le (Set β) (@Set.instLE β) (Y i)
                                    (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁ (fun {X : Set α} => @hD₀nomin X)
                                      (fun {X : Set β} => @hD₁nomin X) X Y j)))
        (@And.intro
          (And
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))))
          (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
            (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                      ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                        (X : Nat → Set α) (Y : Nat → Set β),
                        (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                            @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                              @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                ∀ (i j : Nat),
                                  Iff
                                    (@LE.le (Set α) (@Set.instLE α) (X i)
                                      (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j))
                                    (@LE.le (Set β) (@Set.instLE β)
                                      (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                        (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                      (Y j)))
          (@And.intro
            (And
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁)))
            (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                  ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                        ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                          (X : Nat → Set α) (Y : Nat → Set β),
                          (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                              @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                  ∀ (i j : Nat),
                                    Iff (@Eq (Set α) (X i) (X j))
                                      (@Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y i)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)))
            (@And.intro
              (And
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁))
              (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                    ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                          ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                            (X : Nat → Set α) (Y : Nat → Set β),
                            (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                  @Set.Nonempty β (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                    @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Eq (Set β)
                                        (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                          (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁))
              (@And.intro
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      ∀ (hD₀nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            ∀ (hD₁nomin : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁)
                              (X : Nat → Set α) (Y : Nat → Set β),
                              (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                  @Set.Nonempty α (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                    @Set.Nonempty β
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                      ∀ (j k : Nat),
                                        Iff
                                          (@Eq (Set β)
                                            (@DomainTheory.NeighbourhoodSystems.XPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y j)
                                            (Y k))
                                          (@Eq (Set α) (X j)
                                            (@DomainTheory.NeighbourhoodSystems.YPseq α β D₀ D₁
                                              (fun {X : Set α} => @hD₀nomin X) (fun {X : Set β} => @hD₁nomin X) X Y k)))
                (∀ {α : Type u_1} {β : Type u_2} (D₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  (D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive α D₀ →
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed α D₀ →
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal α D₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive β D₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.DiffClosed β D₁ →
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.NoMinimal β D₁ →
                              ∀ (X : Nat → Set α) (Y : Nat → Set β),
                                (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ (X n)) →
                                  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ (Y n)) →
                                    @Set.Nonempty α
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                      @Set.Nonempty β
                                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                        (∀ (S : Set α),
                                            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D₀ S)
                                              (∃ (n : Nat), @Eq (Set α) S (X n))) →
                                          (∀ (S : Set β),
                                              Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β D₁ S)
                                                (∃ (n : Nat), @Eq (Set β) S (Y n))) →
                                            @Eq (Set α) (X (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master α D₀) →
                                              @Eq (Set β) (Y (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β D₁) →
                                                @DomainTheory.NeighbourhoodSystems.Isomorphic α β D₀ D₁)
                @DomainTheory.NeighbourhoodSystems.XPseq_eq_Y_iff_X_eq_YPseq
                @DomainTheory.NeighbourhoodSystems.isomorphic_812c)
              @DomainTheory.NeighbourhoodSystems.XPseq_zero)
            @DomainTheory.NeighbourhoodSystems.X_eq_iff_XPseq_eq)
          @DomainTheory.NeighbourhoodSystems.X_subset_YPseq_iff_XPseq_subset_Y)
        @DomainTheory.NeighbourhoodSystems.YPseq_subset_X_iff_Y_subset_XPseq)
      @DomainTheory.NeighbourhoodSystems.YPseq_zero)
    @DomainTheory.NeighbourhoodSystems.exists_inter_index_X)
  @DomainTheory.NeighbourhoodSystems.exists_inter_index_Y

end DomainTheory.NeighbourhoodSystems
