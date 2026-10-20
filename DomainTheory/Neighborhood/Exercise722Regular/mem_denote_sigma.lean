/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722
import Mathlib.Logic.Encodable.Basic
import DomainTheory.Neighborhood.Exercise722Regular.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722


















/-- `denote .sigma = Σ` contains every word. -/
theorem mem_denote_sigma (w : List Bool) : w ∈ denote .sigma := Set.mem_univ w

end Exercise722
end DomainTheory.Neighborhood
