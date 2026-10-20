/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Approximable
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Example24.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Example24

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- **`10` terminates the run and emits the `0`, whatever follows.** `out([1,0]++τ) = 0::τ`, for
every tail `τ`. (Exercise 2.17's third equation, at the token level.) -/
theorem out_append_trueFalse (τ : Str) : out ([true, false] ++ τ) = false :: τ := rfl

end DomainTheory.Neighborhood.Example24
