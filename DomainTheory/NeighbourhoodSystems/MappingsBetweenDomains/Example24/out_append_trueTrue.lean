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








/-- **A second consecutive `1` changes nothing.** `out([1,1]++τ) = out([1]++τ)`: once inside the
run of `1`'s, an extra `1` is simply swallowed by `del`. (Exercise 2.17's second equation, at the
token level — the recursive step behind the uniqueness argument for `runMap`.) -/
theorem out_append_trueTrue (τ : Str) : out ([true, true] ++ τ) = out ([true] ++ τ) := rfl

end DomainTheory.Neighborhood.Example24
