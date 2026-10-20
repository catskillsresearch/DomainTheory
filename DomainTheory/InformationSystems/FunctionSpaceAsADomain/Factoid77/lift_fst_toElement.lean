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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
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

theorem lift_fst_toElement (A : InfoSysObj.{u}) {Y Y' : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (p : (productSystem A.sys Y'.sys).Element) :
    (fstMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
            (acomp (sndMap A.sys Y'.sys) f)).toElement p) =
      (fstMap A.sys Y'.sys).toElement p := by
  have e :
      acomp (pairMap A.sys Y.sys (fstMap A.sys Y'.sys) (acomp (sndMap A.sys Y'.sys) f))
        (fstMap A.sys Y.sys) =
      fstMap A.sys Y'.sys := by
    simp only [acomp, comp_fstMap_pairMap]
  calc
    (fstMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
          (acomp (sndMap A.sys Y'.sys) f)).toElement p) =
      (acomp (pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
        (acomp (sndMap A.sys Y'.sys) f)) (fstMap A.sys Y.sys)).toElement p :=
      (acomp_toElement _ _ _).symm
    _ = (fstMap A.sys Y'.sys).toElement p := congrArg (fun φ => φ.toElement p) e

end InfoSys

end DomainTheory.InformationSystems
