
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.pair_after_swap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap_acomp_swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHomToProdHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurry_curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_fst_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swap_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodElementToTensorElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorLeft_map_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.lift_fst_toElement

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

/-- Inverse of `curryRight`. -/
noncomputable def uncurryRight (A Y Z : InfoSysObj.{u}) (k : Y ⟶ InfoSysObj.exp A Z) :
    A ⊗ Y ⟶ Z :=
  prodHomToTensorHom A Y Z (uncurryProduct A Y Z k)


theorem uncurryRight.toElement (A Y Z : InfoSysObj.{u})
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

theorem uncurryRight.curryRight (A Y Z : InfoSysObj.{u}) (h : A ⊗ Y ⟶ Z) :
    uncurryRight A Y Z (InfoSys.curryRight A Y Z h) = h := by
  unfold uncurryRight InfoSys.curryRight uncurryProduct curryProduct
  rw [uncurry_curryMap, ← acomp.assoc, swapMap_acomp_swapMap, id_acomp]
  unfold prodHomToTensorHom tensorHomToProdHom
  simp

theorem uncurryRight.comp_left (A : InfoSysObj.{u}) {Y Y' Z : InfoSysObj.{u}}
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
    rw [uncurryRight.toElement A Y' Z (f ≫ g) p,
      uncurryRight.toElement A Y Z g q]
    simp only [q, tensorElementToProdElement.prodElementToTensorElement]
    rw [swap_fst_toElement, swap_snd_toElement, swap_fst_toElement, swap_snd_toElement,
      lift_snd_toElement A f p', lift_fst_toElement A f p']
    simp only [CategoryStruct.comp, acomp.toElement]
    rfl
  calc
    (uncurryRight A Y' Z (f ≫ g)).toElement p =
        (uncurryRight A Y Z g).toElement q := hgoal
    _ = ((tensorLeft A).map f ≫ uncurryRight A Y Z g).toElement p := by
      rw [tensorLeft_map_eq, productMapToTensorMap.comp.toElement]

end InfoSys

end DomainTheory.InformationSystems
