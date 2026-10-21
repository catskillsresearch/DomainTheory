/-ai
Transporting a map between products to a map between the corresponding tensor products, and evaluating at a tensor element, equals transporting back the evaluation of the original map at the corresponding product element.

Unfold the transports. After substituting the equalities of tensor maps with product maps and of tensor elements with product elements, both sides are definitionally equal.

The file also introduces the closed structure on an information-system object, with right adjoint the exponential functor and with the tensor-exponential adjunction, and the monoidal closed structure on the category of information systems in which every object is closed. This packages the cartesian closed category of information systems and approximable maps.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.terminalLimitCone
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productLimitCone
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHomToProdHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpEquiv
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.expFunctor
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpAdjunction
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prod
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.unit
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_id
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_assoc
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_swap_fst
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_swap_snd
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap_acomp_swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curry_uncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHom_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement_prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorMap_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap_comp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight_uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorLeft_map_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.pair_after_swap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_comp_left
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpEquiv_natural
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorMap_eq_productMap

@[expose] public section

/-!
# Factoid 7.7 — cartesian closed structure (stretch goal)

**Scott 1982 (*Categories again*).** Props 6.2 and Theorem 7.2 (with unit `1` from
Factoid 6.5) show that information systems and approximable maps form a cartesian
closed category. This file packages that as Mathlib `Category`,
`CartesianMonoidalCategory`, and `MonoidalClosed`.

**Constructivity note.** The Scott-side data (products, curry/uncurry) is constructive.
Wiring it through Mathlib’s `CategoryTheory` (chosen finite products / adjunction
constructors) introduces `Classical.choice`. This is an artifact of Lean’s category
library, not of Scott’s argument; the constructive core of the formalization is
unaffected.
-/

universe u

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

/-! ## Bundled objects -/


attribute [instance] InfoSysObj.decEq

namespace InfoSysObj




end InfoSysObj

/-! ## Diagrammatic composition (`f.acomp g` = apply `f` then `g` = `f ≫ g`) -/

namespace ApproximableMap













end ApproximableMap

open ApproximableMap

/-! ## Category -/


attribute [instance] instCategoryInfoSysObj

/-! ## Finite products -/













theorem productMapToTensorMap_toElement (A Y Y' : InfoSysObj.{u})
    (f : ApproximableMap (productSystem A.sys Y.sys) (productSystem A.sys Y'.sys))
    (p : (A ⊗ Y).sys.Element) :
    (productMapToTensorMap A Y Y' f).toElement p =
      prodElementToTensorElement A Y'
        (f.toElement (tensorElementToProdElement A Y p)) := by
  unfold productMapToTensorMap prodElementToTensorElement tensorElementToProdElement
  generalize tensorMap_eq_productMap A Y Y' = eh
  generalize tensorElement_eq_productElement A Y = es
  generalize tensorElement_eq_productElement A Y' = et
  cases eh
  cases es
  cases et
  rfl





/-! ## Braided curry (Mathlib convention) -/







/-! ## Left naturality of uncurry / MonoidalClosed -/









noncomputable instance (A : InfoSysObj.{u}) : Closed A where
  rightAdj := expFunctor A
  adj := tensorExpAdjunction A

noncomputable instance : MonoidalClosed InfoSysObj.{u} where
  closed _ := inferInstance
end InfoSys
end DomainTheory.InformationSystems
