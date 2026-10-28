module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap_acomp_swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curry_uncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHom_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorMap_eq_productMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight_uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorLeft_map_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.pair_after_swap_toElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

namespace InfoSysObj

end InfoSysObj
namespace ApproximableMap

end ApproximableMap

open ApproximableMap

attribute [instance] instCategoryInfoSysObj

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

noncomputable instance (A : InfoSysObj.{u}) : Closed A where
  rightAdj := expFunctor A
  adj := tensorExpAdjunction A

noncomputable instance : MonoidalClosed InfoSysObj.{u} where
  closed _ := inferInstance

end InfoSys

end DomainTheory.InformationSystems
