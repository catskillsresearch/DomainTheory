/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid65
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import DomainTheory.InformationSystems.Factoid77.Basic


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

theorem tensorObj_eq_prod (A Y : InfoSysObj.{u}) : A ⊗ Y = InfoSysObj.prod A Y := rfl

end InfoSys
end DomainTheory.InformationSystems
