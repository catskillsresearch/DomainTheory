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
import DomainTheory.Neighborhood.Exercise722DFA.singleDFA_accepts


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability







theorem singleDFA_accepts_denote (σ : List Bool) : (singleDFA σ).accepts = denote (.single σ) := by
  rw [singleDFA_accepts]; exact (denote_single σ).symm

end Exercise722
end DomainTheory.Neighborhood
