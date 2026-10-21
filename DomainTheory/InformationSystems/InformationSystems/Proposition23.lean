/-ai
The empty set set-entails the singleton of the least token. If u is consistent and u set-entails v, then the constructive union of u with v is consistent. A consistent finite set set-entails itself. Set-level entailment is transitive: if u and v are consistent, u set-entails v, and v set-entails w, then u set-entails w. Set-level entailment is monotone: if u and u' are consistent, u is contained in u', u set-entails v, and v' is contained in v, then u' set-entails v'. If a finite set set-entails both v and v', then it set-entails their constructive union.

The numbered name theorem_23 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_i
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iv
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_v
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_vi

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_23.{u_1} : And
  (And
    (And
      (And
        (And
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v)))
        (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α},
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u u))
      (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
        {u v w : Finset α},
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) v →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys v w →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u w))
    (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
      {u u' v v' : Finset α},
      @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
          (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u' →
          @LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u u' →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @LE.le (Finset α)
                  (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) v' v →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u' v'))
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u v v' : Finset α},
    @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
      @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v' →
        @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u
          (@DomainTheory.InformationSystems.Constructive.funion α inst v v')) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v)))
        (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α},
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u u))
      (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
        {u v w : Finset α},
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) v →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys v w →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u w))
    (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
      {u u' v v' : Finset α},
      @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
          (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u' →
          @LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u u' →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @LE.le (Finset α)
                  (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) v' v →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u' v'))
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u v v' : Finset α},
    @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
      @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v' →
        @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u
          (@DomainTheory.InformationSystems.Constructive.funion α inst v v'))
  (@And.intro
    (And
      (And
        (And
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v)))
        (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α},
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u u))
      (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
        {u v w : Finset α},
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) v →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys v w →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u w))
    (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
      {u u' v v' : Finset α},
      @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
          (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u' →
          @LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u u' →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @LE.le (Finset α)
                  (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) v' v →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u' v')
    (@And.intro
      (And
        (And
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v)))
        (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α},
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u u))
      (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
        {u v w : Finset α},
        @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
            (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) v →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys v w →
                @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u w)
      (@And.intro
        (And
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v)))
        (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α},
          @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
              (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u u)
        (@And.intro
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
            @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys
              (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α)
                (@DomainTheory.InformationSystems.InfoSys.bot α inst sys)))
          (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
            {u v : Finset α},
            @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u →
              @DomainTheory.InformationSystems.InfoSys.EntSet α inst sys u v →
                @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
                  (@DomainTheory.InformationSystems.InfoSys.Con α inst sys)
                  (@DomainTheory.InformationSystems.Constructive.funion α inst u v))
          @DomainTheory.InformationSystems.InfoSys.proposition_2_3_i
          @DomainTheory.InformationSystems.InfoSys.proposition_2_3_ii)
        @DomainTheory.InformationSystems.InfoSys.proposition_2_3_iii)
      @DomainTheory.InformationSystems.InfoSys.proposition_2_3_iv)
    @DomainTheory.InformationSystems.InfoSys.proposition_2_3_v)
  @DomainTheory.InformationSystems.InfoSys.proposition_2_3_vi

end DomainTheory.InformationSystems.InfoSys
