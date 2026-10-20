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
public import DomainTheory.InformationSystems.Factoid77.tensorExpEquiv
public import DomainTheory.InformationSystems.Factoid77.tensorExpEquiv_natural
public import DomainTheory.InformationSystems.Factoid77.expFunctor
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

noncomputable def tensorExpAdjunction (A : InfoSysObj.{u}) :
    tensorLeft A ⊣ expFunctor A :=
  Adjunction.adjunctionOfEquivRight (F := tensorLeft A) (tensorExpEquiv A)
    fun _Y' _Y _Z f g => by
      simpa using tensorExpEquiv_natural A f g

end InfoSys

end DomainTheory.InformationSystems
