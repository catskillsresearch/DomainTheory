/-ai
Right uncurry preserves precomposition on the left: the uncurry of f followed by g equals left tensoring of f followed by the uncurry of g.

The two sides are compared on elements. For a tensor element p, let p' be its product image and let q be the tensor image of the pairing of the first projection with the second projection composed with f, applied to p'. The elementwise formula for right uncurry, cancellation of the product–tensor round trip, the swap formulas for both projections, and the elementwise formulas for that pairing show that uncurrying the composite at p agrees with uncurrying g at q. The description of left tensoring as that pairing, and the elementwise formula for a product map followed by a tensor map, identify the remaining side with the composite.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement_prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap_comp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorLeft_map_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_toElement
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

theorem uncurryRight_comp_left (A : InfoSysObj.{u}) {Y Y' Z : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (g : Y ⟶ InfoSysObj.exp A Z) :
    uncurryRight A Y' Z (f ≫ g) = (tensorLeft A).map f ≫ uncurryRight A Y Z g := by
  refine (ext_iff_toElement _ _).2 fun p => ?_
  let p' := tensorElementToProdElement A Y' p
  set lift :=
    pairMap A.sys Y.sys (fstMap A.sys Y'.sys) (acomp (sndMap A.sys Y'.sys) f)
  let q := prodElementToTensorElement A Y (lift.toElement p')
  have hgoal :
      (uncurryRight A Y' Z (f ≫ g)).toElement p =
        (uncurryRight A Y Z g).toElement q := by
    rw [uncurryRight_toElement A Y' Z (f ≫ g) p,
      uncurryRight_toElement A Y Z g q]
    simp only [q, tensorElementToProdElement_prodElementToTensorElement]
    rw [swap_fst_toElement, swap_snd_toElement, swap_fst_toElement, swap_snd_toElement,
      lift_snd_toElement A f p', lift_fst_toElement A f p']
    simp only [CategoryStruct.comp, acomp_toElement]
    rfl
  calc
    (uncurryRight A Y' Z (f ≫ g)).toElement p =
        (uncurryRight A Y Z g).toElement q := hgoal
    _ = ((tensorLeft A).map f ≫ uncurryRight A Y Z g).toElement p := by
      rw [tensorLeft_map_eq, productMapToTensorMap_comp_toElement]

end InfoSys

end DomainTheory.InformationSystems
