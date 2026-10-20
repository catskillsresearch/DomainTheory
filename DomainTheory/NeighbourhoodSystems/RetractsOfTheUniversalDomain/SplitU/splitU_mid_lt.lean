/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.UComputablePresentation
public import DomainTheory.Neighborhood.SplitU.Basic
public import DomainTheory.Neighborhood.SplitU.splitU_p0_lt

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

















theorem splitU_mid_lt (n : ℕ) :
    decodeRat (splitMidCode n) < (decodeRatPair (firstElemCode (canonCode n))).2 := by
  show decodeRat (splitMidCode n) < decodeRat (firstElemCode (canonCode n)).unpair.2
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact add_div_two_lt_right.mpr h

end DomainTheory.Neighborhood
