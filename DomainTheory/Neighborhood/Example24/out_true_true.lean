/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example24.Basic


namespace DomainTheory.Neighborhood.Example24

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- Cons-form restatement of `out_append_trueTrue`, for peeling one token at a time in `key`. -/
theorem out_true_true (t : Str) : out (true :: true :: t) = out (true :: t) := rfl

end DomainTheory.Neighborhood.Example24
