/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise419.Basic


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (ii) for `{0,1}*`.** Each successor `b ::·` is injective. -/
theorem peano_cons_injective {b : Bool} {σ τ : Str} (h : b :: σ = b :: τ) : σ = τ :=
  (List.cons.injEq b σ b τ).mp h |>.2

end DomainTheory.Neighborhood.Exercise419
