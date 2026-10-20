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












/-- `{0,1} ∩ {1,2} = {1}`. -/
theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by ext x; fin_cases x <;> simp [a, b]

end DomainTheory.Neighborhood.Exercise119
