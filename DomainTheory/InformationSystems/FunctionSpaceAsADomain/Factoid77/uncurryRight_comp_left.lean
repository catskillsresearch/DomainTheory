/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
