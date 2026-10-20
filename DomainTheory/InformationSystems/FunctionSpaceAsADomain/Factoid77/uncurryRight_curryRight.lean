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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_assoc
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap_acomp_swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHomToProdHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
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

theorem uncurryRight_curryRight (A Y Z : InfoSysObj.{u}) (h : A ⊗ Y ⟶ Z) :
    uncurryRight A Y Z (curryRight A Y Z h) = h := by
  unfold uncurryRight curryRight uncurryProduct curryProduct
  rw [uncurry_curryMap, ← acomp_assoc, swapMap_acomp_swapMap, id_acomp]
  unfold prodHomToTensorHom tensorHomToProdHom
  simp

end InfoSys

end DomainTheory.InformationSystems
