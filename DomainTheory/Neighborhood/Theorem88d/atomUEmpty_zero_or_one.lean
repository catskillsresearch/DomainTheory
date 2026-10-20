/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88b
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)






















































theorem atomUEmpty_zero_or_one (n k : ℕ) : atomUEmpty P n k = 0 ∨ atomUEmpty P n k = 1 := by
  have h := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  unfold atomUEmpty
  omega

end DomainTheory.Neighborhood
