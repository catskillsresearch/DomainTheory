
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.pair_after_swap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
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

theorem uncurryRight_toElement (A Y Z : InfoSysObj.{u})
    (φ : Y ⟶ InfoSysObj.exp A Z) (q : (A ⊗ Y).sys.Element) :
    (uncurryRight A Y Z φ).toElement q =
      (element_toApproxMap A.sys Z.sys
          (φ.toElement ((fstMap Y.sys A.sys).toElement
            ((swapMap A.sys Y.sys).toElement
              (tensorElementToProdElement A Y q))))).toElement
        ((sndMap Y.sys A.sys).toElement
          ((swapMap A.sys Y.sys).toElement
            (tensorElementToProdElement A Y q))) := by
  rw [show (uncurryRight A Y Z φ).toElement q =
      (uncurryProduct A Y Z φ).toElement
        (tensorElementToProdElement A Y q) by
    exact prodHomToTensorHom.toElement A Y Z (uncurryProduct A Y Z φ) q]
  unfold uncurryProduct
  rw [acomp.toElement]
  unfold uncurryMap
  rw [comp.toElement,
    pair_after_swap_toElement A Y Z φ (tensorElementToProdElement A Y q),
    applyMap_toElement]

end InfoSys

end DomainTheory.InformationSystems
