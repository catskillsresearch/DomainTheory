/-ai
Evaluating the right uncurry of a morphism φ at a tensor element q equals evaluating the approximable map named by φ at the first component of the swapped product image of q, on the second component of that same swapped image.

Transport along the product–tensor hom equality replaces the tensor evaluation by the product uncurry on the product image of q. Unfolding that product uncurry, the elementwise composition law, the formula for a pair after a swap, and the elementwise formula for application give the stated value.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.pair_after_swap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

@[expose] public section

set_option linter.unusedSectionVars false

universe u

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
    exact prodHomToTensorHom_toElement A Y Z (uncurryProduct A Y Z φ) q]
  unfold uncurryProduct
  rw [acomp_toElement]
  unfold uncurryMap
  rw [comp_toElement,
    pair_after_swap_toElement A Y Z φ (tensorElementToProdElement A Y q),
    applyMap_toElement]

end InfoSys

end DomainTheory.InformationSystems
