/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.IntervalPrimrec
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.UComputablePresentation.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem




























/-- Every pair in `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point). -/
theorem forall_lt_decodeQPairList_canonListCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonListCode c), p.1 < p.2 := fun p hp => by
  obtain ⟨p0, -, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
  exact hcond

end DomainTheory.Neighborhood
