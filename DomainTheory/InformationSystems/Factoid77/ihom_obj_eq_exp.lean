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
public import DomainTheory.InformationSystems.Factoid77.Basic

@[expose] public section


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

































/-- The Mathlib exponential is Scott’s function space on objects. -/
theorem ihom_obj_eq_exp (A B : InfoSysObj.{u}) :
    (ihom A).obj B = InfoSysObj.exp A B :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
