module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_assoc
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap_acomp_swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curry_uncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHomToProdHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
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

theorem curryRight_uncurryRight (A Y Z : InfoSysObj.{u}) (k : Y ⟶ InfoSysObj.exp A Z) :
    curryRight A Y Z (uncurryRight A Y Z k) = k := by
  unfold curryRight uncurryRight
  rw [show tensorHomToProdHom A Y Z
      (prodHomToTensorHom A Y Z (uncurryProduct A Y Z k)) =
      uncurryProduct A Y Z k by
    unfold tensorHomToProdHom prodHomToTensorHom
    simp]
  unfold curryProduct uncurryProduct
  have hred :
      acomp (swapMap Y.sys A.sys)
        (acomp (swapMap A.sys Y.sys) (uncurryMap Y.sys A.sys Z.sys k)) =
        uncurryMap Y.sys A.sys Z.sys k := by
    calc
      acomp (swapMap Y.sys A.sys)
            (acomp (swapMap A.sys Y.sys) (uncurryMap Y.sys A.sys Z.sys k))
          = acomp (acomp (swapMap Y.sys A.sys) (swapMap A.sys Y.sys))
              (uncurryMap Y.sys A.sys Z.sys k) := (acomp_assoc _ _ _).symm
      _ = acomp (idMap (productSystem Y.sys A.sys))
              (uncurryMap Y.sys A.sys Z.sys k) := by rw [swapMap_acomp_swapMap]
      _ = uncurryMap Y.sys A.sys Z.sys k := id_acomp _
  refine Eq.trans (congrArg (curryMap Y.sys A.sys Z.sys) hred)
    (curry_uncurry Y.sys A.sys Z.sys k)

end InfoSys

end DomainTheory.InformationSystems
