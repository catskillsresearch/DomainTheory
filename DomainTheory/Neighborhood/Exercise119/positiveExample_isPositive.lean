/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise119.Basic


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood.Exercise119

open DomainTheory.Neighborhood



theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl

end DomainTheory.Neighborhood.Exercise119
