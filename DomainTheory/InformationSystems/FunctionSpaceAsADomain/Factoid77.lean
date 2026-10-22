module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.ihom_obj_eq_exp

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_77.{u} : ∀ (A B : DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}),
  @Eq.{u + 2} DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
    (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
      DomainTheory.InformationSystems.InfoSys.instCategoryInfoSysObj.{u}
      DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
      DomainTheory.InformationSystems.InfoSys.instCategoryInfoSysObj.{u}
      (@CategoryTheory.ihom.{u, u + 1} DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
        DomainTheory.InformationSystems.InfoSys.instCategoryInfoSysObj.{u}
        (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
          DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
          DomainTheory.InformationSystems.InfoSys.instCategoryInfoSysObj.{u}
          (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u, u + 1}
            DomainTheory.InformationSystems.InfoSys.InfoSysObj.{u}
            DomainTheory.InformationSystems.InfoSys.instCategoryInfoSysObj.{u}
            DomainTheory.InformationSystems.InfoSys.instCartesianMonoidalCategoryInfoSysObj.{u}))
        A (DomainTheory.InformationSystems.InfoSys.instClosedInfoSysObj.{u} A))
      B)
    (A.exp B) :=
  DomainTheory.InformationSystems.InfoSys.ihom_obj_eq_exp.{u}

end DomainTheory.InformationSystems.InfoSys
