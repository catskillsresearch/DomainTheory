/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise118.Basic


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood






theorem triSys_master : triSys.master = (Set.univ : Set (Fin 3)) := rfl

end DomainTheory.Neighborhood
