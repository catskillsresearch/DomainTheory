/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Theorem86.Basic
import DomainTheory.Neighborhood.Theorem86.sub_sub
import DomainTheory.Neighborhood.Theorem86.isFinitaryProjection_of_sub_eq_self


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`sub` is itself a finitary projection on `E → E`'s range** (Theorem 8.6's remark that `sub`
restricted to its own range is the identity, i.e. `sub` "is" a projection onto the finitary
projections): applying `sub` twice is the same as once (`sub_sub`), and every `sub f` is already a
fixed point of `sub` (feed `isFinitaryProjection_of_sub_eq_self (sub_sub f)` back through
`sub_eq_self_iff_isFinitaryProjection`) — i.e. `sub f` is *always* a finitary projection, for any
`f`, needing no hypothesis on `f` at all. -/
theorem isFinitaryProjection_sub (f : ApproximableMap E E) : IsFinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)

end DomainTheory.Neighborhood
