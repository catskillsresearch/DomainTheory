/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.Factoid77.InfoSysObj
import all DomainTheory.InformationSystems.Factoid77.tensorHom_eq_productMap
public import DomainTheory.InformationSystems.Factoid77.tensorElement_eq_productElement
public import DomainTheory.InformationSystems.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.Factoid77.tensorElementToProdElement
public import DomainTheory.InformationSystems.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.Factoid77.instCartesianMonoidalCategoryInfoSysObj

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

theorem prodHomToTensorHom_toElement (A Y Z : InfoSysObj.{u})
    (h : ApproximableMap (productSystem A.sys Y.sys) Z.sys)
    (p : (A ⊗ Y).sys.Element) :
    (prodHomToTensorHom A Y Z h).toElement p =
      h.toElement (tensorElementToProdElement A Y p) := by
  unfold prodHomToTensorHom tensorElementToProdElement
  generalize tensorHom_eq_productMap A Y Z = eh
  generalize tensorElement_eq_productElement A Y = ee
  cases eh
  cases ee
  rfl

end InfoSys

end DomainTheory.InformationSystems
