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
public import DomainTheory.InformationSystems.Factoid77.acomp

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

namespace ApproximableMap

theorem acomp_toElement {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (x : A.Element) :
    (acomp f g).toElement x = g.toElement (f.toElement x) :=
  comp_toElement g f x

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
