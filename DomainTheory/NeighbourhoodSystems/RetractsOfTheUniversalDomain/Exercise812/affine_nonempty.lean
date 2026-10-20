/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition87
public import DomainTheory.Neighborhood.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.Neighborhood.Exercise812.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem




theorem affine_nonempty {k ℓ : ℕ} (hℓ : ℓ < 2 ^ k) : (affine k ℓ).Nonempty :=
  ⟨ℓ, Nat.mod_eq_of_lt hℓ⟩

end DomainTheory.Neighborhood
