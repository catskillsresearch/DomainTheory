module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.ext_iff_toElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.le_iff_toElement_le
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.rel_iff_closure_le

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_53.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B) f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x)))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.Le α β inst inst_1 A B f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @LE.le (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
              (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
                (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement β inst_1 B)))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x))))
  (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
    {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
    (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B) {u : Finset α} {v : Finset β}
    (hu :
      @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
        (@DomainTheory.InformationSystems.InfoSys.Con α inst A) u)
    (hv :
      @Membership.mem (Finset β) (Set (Finset β)) (@Set.instMembership (Finset β))
        (@DomainTheory.InformationSystems.InfoSys.Con β inst_1 B) v),
    Iff (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.rel α β inst inst_1 A B f u v)
      (@LE.le (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
        (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
          (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement β inst_1 B)))
        (@DomainTheory.InformationSystems.InfoSys.closure β inst_1 B v hv)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f
          (@DomainTheory.InformationSystems.InfoSys.closure α inst A u hu)))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B) f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x)))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.Le α β inst inst_1 A B f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @LE.le (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
              (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
                (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement β inst_1 B)))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x))))
  (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
    {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
    (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B) {u : Finset α} {v : Finset β}
    (hu :
      @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
        (@DomainTheory.InformationSystems.InfoSys.Con α inst A) u)
    (hv :
      @Membership.mem (Finset β) (Set (Finset β)) (@Set.instMembership (Finset β))
        (@DomainTheory.InformationSystems.InfoSys.Con β inst_1 B) v),
    Iff (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.rel α β inst inst_1 A B f u v)
      (@LE.le (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
        (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
          (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement β inst_1 B)))
        (@DomainTheory.InformationSystems.InfoSys.closure β inst_1 B v hv)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f
          (@DomainTheory.InformationSystems.InfoSys.closure α inst A u hu))))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B) f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x)))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (f g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      Iff (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.Le α β inst inst_1 A B f g)
        (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @LE.le (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
              (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
                (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement β inst_1 B)))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B g x)))
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.ext_iff_toElement
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.le_iff_toElement_le)
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.rel_iff_closure_le

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
