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




theorem sigmaDFA_accepts_denote : sigmaDFA.accepts = denote .sigma := by
  rw [sigmaDFA_accepts, denote_sigma]

end Exercise722
end DomainTheory.Neighborhood
