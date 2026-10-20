/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88.Basic
public import DomainTheory.Neighborhood.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.Neighborhood.Definition610
public import DomainTheory.Neighborhood.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.Neighborhood.Theorem88a.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)




theorem idxSet_nonempty (n : ℕ) : (idxSet e n).Nonempty := ⟨n, self_mem_idxSet e n⟩

end Reencode
end DomainTheory.Neighborhood
