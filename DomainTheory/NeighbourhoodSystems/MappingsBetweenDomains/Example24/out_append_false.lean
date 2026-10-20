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








/-- **A leading `0` always emits it and continues copying.** `out([0]++τ) = 0::out τ`, for every
tail `τ`. (Exercise 2.17's first equation, at the token level.) -/
theorem out_append_false (τ : Str) : out ([false] ++ τ) = false :: out τ := rfl

end DomainTheory.Neighborhood.Example24
