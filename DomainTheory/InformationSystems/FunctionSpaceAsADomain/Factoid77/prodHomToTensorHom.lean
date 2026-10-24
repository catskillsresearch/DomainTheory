module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHom_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement

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

def prodHomToTensorHom (A Y Z : InfoSysObj.{u})
    (h : ApproximableMap (productSystem A.sys Y.sys) Z.sys) : A ⊗ Y ⟶ Z :=
  cast (tensorHom_eq_productMap A Y Z).symm h

end InfoSys

end DomainTheory.InformationSystems

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

theorem prodHomToTensorHom.toElement (A Y Z : InfoSysObj.{u})
    (h : ApproximableMap (productSystem A.sys Y.sys) Z.sys)
    (p : (A ⊗ Y).sys.Element) :
    (prodHomToTensorHom A Y Z h).toElement p =
      h.toElement (tensorElementToProdElement A Y p) := by
  unfold prodHomToTensorHom tensorElementToProdElement
  generalize tensorHom_eq_productMap A Y Z = eh
  generalize tensorElement_eq_productElement A Y = ee
  cases eh
  cases ee
  rfl

end InfoSys

end DomainTheory.InformationSystems
