/-ai
Two elements have a common upper bound if and only if the union of their carriers is finitely consistent.

The numbered name theorem_43 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.exists_join_iff

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_43.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (x y : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
  Iff
    (∃ (z : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
      And
        (@LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
          (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
            (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
              (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst sys)))
          x z)
        (@LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
          (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
            (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
              (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst sys)))
          y z))
    (Nonempty
      (@DomainTheory.InformationSystems.InfoSys.IsFinitelyConsistent α inst sys
        (@Union.union (Set α) (@Set.instUnion α) (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x)
          (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys y)))) :=
  @DomainTheory.InformationSystems.InfoSys.exists_join_iff

end DomainTheory.InformationSystems.InfoSys
