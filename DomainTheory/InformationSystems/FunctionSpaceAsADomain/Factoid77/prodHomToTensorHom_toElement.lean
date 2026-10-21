/-ai
A map out of a product, transported to a morphism out of the tensor product and evaluated at a tensor element, equals the original map evaluated at the corresponding product element.

Unfold the transports. After substituting the equalities of tensor homs with product maps and of tensor elements with product elements, both sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
import all DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHom_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
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

theorem prodHomToTensorHom_toElement (A Y Z : InfoSysObj.{u})
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
