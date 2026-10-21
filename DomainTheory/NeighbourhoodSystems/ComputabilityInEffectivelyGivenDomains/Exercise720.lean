/-ai
If the base domain is effectively given, the flattening combinator is a computable map from the canonical presentation of the double power domain into the canonical presentation of the power domain. If a presentation of the power domain enumerates the canonical power-domain neighbourhoods, then the flattening combinator relates the double-power neighbourhood coded by n to the power neighbourhood coded by m exactly when every index of every list coded inside n is contained, as a base neighbourhood, in some index of the list coded by m. On nested finite generators, the flattening combinator relates the union of the power-domain up-sets of the inner unions to the union of the up-sets of a list exactly when every neighbourhood in every inner list is contained in some neighbourhood of the outer list.

The numbered name example_720 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.unionMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.unionMap_rel_Ypd_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.unionMap_rel_fin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_720.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {LS : List (List (Set α))}
    {LY : List (Set α)},
    (∀ (l : List (Set α)),
        @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
          ∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set α),
          @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.unionMap α V)
            (⋃ (l : List (Set α)),
              ⋃ (_ : @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (⋃ (X : Set α),
                    ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            (⋃ (Y : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V Y))
          (∀ (l : List (Set α)),
            @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
              ∀ (X : Set α),
                @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
                  ∃ (Y : Set α),
                    And (@Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y)
                      (@LE.le (Set α) (@Set.instLE α) X Y))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {LS : List (List (Set α))}
    {LY : List (Set α)},
    (∀ (l : List (Set α)),
        @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
          ∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set α),
          @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.unionMap α V)
            (⋃ (l : List (Set α)),
              ⋃ (_ : @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (⋃ (X : Set α),
                    ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            (⋃ (Y : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V Y))
          (∀ (l : List (Set α)),
            @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
              ∀ (X : Set α),
                @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
                  ∃ (Y : Set α),
                    And (@Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y)
                      (@LE.le (Set α) (@Set.instLE α) X Y)))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
    @DomainTheory.NeighbourhoodSystems.unionMap_isComputable @DomainTheory.NeighbourhoodSystems.unionMap_rel_Ypd_iff)
  @DomainTheory.NeighbourhoodSystems.unionMap_rel_fin

end DomainTheory.NeighbourhoodSystems
