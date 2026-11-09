module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

open ApproximableMap

attribute [instance] instCategoryInfoSysObj

attribute [instance] instCartesianMonoidalCategoryInfoSysObj

theorem lift_snd_toElement (A : InfoSysObj.{u}) {Y Y' : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (p : (productSystem A.sys Y'.sys).Element) :
    (productSystem.sndMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (productSystem.fstMap A.sys Y'.sys)
            (acomp (productSystem.sndMap A.sys Y'.sys) f)).toElement p) =
      f.toElement ((productSystem.sndMap A.sys Y'.sys).toElement p) := by
  have e :
      acomp (pairMap A.sys Y.sys (productSystem.fstMap A.sys Y'.sys) (acomp (productSystem.sndMap A.sys Y'.sys) f))
        (productSystem.sndMap A.sys Y.sys) =
      acomp (productSystem.sndMap A.sys Y'.sys) f := by
    simp only [acomp, pairMap.comp_snd]
  calc
    (productSystem.sndMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (productSystem.fstMap A.sys Y'.sys)
          (acomp (productSystem.sndMap A.sys Y'.sys) f)).toElement p) =
      (acomp (pairMap A.sys Y.sys (productSystem.fstMap A.sys Y'.sys)
        (acomp (productSystem.sndMap A.sys Y'.sys) f)) (productSystem.sndMap A.sys Y.sys)).toElement p :=
      (acomp.toElement _ _ _).symm
    _ = (acomp (productSystem.sndMap A.sys Y'.sys) f).toElement p := congrArg (fun φ => φ.toElement p) e
    _ = f.toElement ((productSystem.sndMap A.sys Y'.sys).toElement p) := acomp.toElement _ _ _

end InfoSys

end DomainTheory.InformationSystems
