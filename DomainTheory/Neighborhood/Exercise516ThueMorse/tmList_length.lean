/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419













theorem tmList_length (n : ℕ) : (tmList n).length = n := by
  rw [tmList, List.length_map, List.length_range]

end DomainTheory.Neighborhood.Exercise516
