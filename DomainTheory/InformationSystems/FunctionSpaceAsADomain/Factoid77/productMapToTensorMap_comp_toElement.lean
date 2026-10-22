
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorMap_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap
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

theorem productMapToTensorMap_comp_toElement (A Y Y' Z : InfoSysObj.{u})
    (f : ApproximableMap (productSystem A.sys Y.sys) (productSystem A.sys Y'.sys))
    (g : A ⊗ Y' ⟶ Z) (p : (A ⊗ Y).sys.Element) :
    (productMapToTensorMap A Y Y' f ≫ g).toElement p =
      g.toElement (prodElementToTensorElement A Y'
        (f.toElement (tensorElementToProdElement A Y p))) := by
  unfold instCategoryInfoSysObj productMapToTensorMap
    prodElementToTensorElement tensorElementToProdElement
  generalize tensorMap_eq_productMap A Y Y' = eh
  generalize tensorElement_eq_productElement A Y = es
  generalize tensorElement_eq_productElement A Y' = et
  cases eh
  cases es
  cases et
  exact acomp_toElement _ _ _

end InfoSys

end DomainTheory.InformationSystems
