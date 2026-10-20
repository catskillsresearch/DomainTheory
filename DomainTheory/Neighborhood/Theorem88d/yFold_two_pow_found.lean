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
public import DomainTheory.Neighborhood.Theorem88d.yFold_found_iff

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)























































theorem yFold_two_pow_found (n : ℕ) : (yFold P n (2 ^ n)).unpair.1 = 1 :=
  (yFold_found_iff P n (2 ^ n)).mpr (exists_atomUEmpty_zero P n)

end DomainTheory.Neighborhood
