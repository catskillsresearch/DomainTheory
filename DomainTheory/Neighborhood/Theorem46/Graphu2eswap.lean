/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Theorem46.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- The construction is symmetric in the two models: `Graph P Q m n` swaps to `Graph Q P n m`.
(This is why the relation is one-one in *both* directions, as Scott notes: "the rôles of `N` and
`M` are completely symmetric".) -/
theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

end PeanoModel
end DomainTheory.Neighborhood
