/-ai
Under the correspondence of a function space with its approximable maps, the combinator sends the point named by a map f to the point named by the power-domain action of f. The power-domain action preserves composition. The power-domain action preserves identity maps. If an approximable map is computable, then its power-domain action is a computable map between the canonical power-domain presentations built from primitive-recursive consistency deciders. If an approximable map is computable, then the relation of its power-domain action on the canonical power-domain codes is recursively enumerable. On the canonical power-domain codes, the power-domain action relates the neighbourhood coded by c to the neighbourhood coded by d exactly when every index in the list coded by c is related by the map to some index in the list coded by d. On finite generators, the power-domain action relates the union of the up-sets of a list to the union of the up-sets of another list exactly when every neighbourhood in the first list is related by the map to some neighbourhood in the second list.

The numbered name example_719 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmapComb_toElementMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_comp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_idMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_isComputable_Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_rel_Ypd_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_rel_fin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_719.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {L₁ : List (Set α)} {L₂ : List (Set β)},
    (∀ (X : Set α),
        @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set β),
          @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
            (⋃ (X : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
            (⋃ (Y : Set β),
              ⋃ (_ : @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y))
          (∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
              ∃ (Y : Set β),
                And (@Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f X Y))) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {L₁ : List (Set α)} {L₂ : List (Set β)},
    (∀ (X : Set α),
        @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set β),
          @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
            (⋃ (X : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
            (⋃ (Y : Set β),
              ⋃ (_ : @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y))
          (∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
              ∃ (Y : Set β),
                And (@Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f X Y)))
  (@And.intro
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
    (@And.intro
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
      (@And.intro
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.IsComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))
        (@And.intro
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)))
          (@And.intro
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            @DomainTheory.NeighbourhoodSystems.PFmapComb_toElementMap @DomainTheory.NeighbourhoodSystems.PFmap_comp)
          @DomainTheory.NeighbourhoodSystems.PFmap_idMap)
        @DomainTheory.NeighbourhoodSystems.PFmap_isComputable)
      @DomainTheory.NeighbourhoodSystems.PFmap_isComputable_Ypd)
    @DomainTheory.NeighbourhoodSystems.PFmap_rel_Ypd_iff)
  @DomainTheory.NeighbourhoodSystems.PFmap_rel_fin

end DomainTheory.NeighbourhoodSystems
