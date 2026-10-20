/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.Exercise812g4
public import DomainTheory.Neighborhood.Exercise813a.Basic
public import DomainTheory.Neighborhood.Exercise813a.testBit_mod_two_pow

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem


/-- Specialization of `testBit_mod_two_pow` used repeatedly below: reducing mod `2^(i+1)` never
disturbs bit `i` itself. -/
theorem testBit_mod_two_pow_succ (n i : ℕ) :
    (n % 2 ^ (i + 1)).testBit i = n.testBit i := by
  rw [testBit_mod_two_pow]; simp

end DomainTheory.Neighborhood
