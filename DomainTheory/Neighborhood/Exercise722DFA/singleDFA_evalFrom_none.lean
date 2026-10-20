/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Regular
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option
import DomainTheory.Neighborhood.Exercise722DFA.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability







/-- The dead state `none` is a sink. -/
theorem singleDFA_evalFrom_none (σ : List Bool) (w : List Bool) :
    (singleDFA σ).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [DFA.evalFrom_cons]; exact ih

end Exercise722
end DomainTheory.Neighborhood
