module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

open ApproximableMap
attribute [instance] InfoSysObj.decEq
attribute [instance] instCategoryInfoSysObj
attribute [instance] instCartesianMonoidalCategoryInfoSysObj

def tensorElementToProdElement (A Y : InfoSysObj.{u})
    (p : (A ⊗ Y).sys.Element) : (productSystem A.sys Y.sys).Element :=
  cast (tensorElement_eq_productElement A Y) p

theorem tensorElementToProdElement.prodElementToTensorElement
    (A Y : InfoSysObj.{u}) (p : (productSystem A.sys Y.sys).Element) :
    tensorElementToProdElement A Y (InfoSys.prodElementToTensorElement A Y p) = p := by
  unfold tensorElementToProdElement InfoSys.prodElementToTensorElement
  simp

end InfoSys


end DomainTheory.InformationSystems
