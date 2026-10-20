/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic
import DomainTheory.Neighborhood.Recursive.decodeList_foldl_mapPairStp


namespace Domain.Recursive



























































































































theorem decodeList_mapPairCode (n c : ℕ) :
    decodeList (mapPairCode n c) = ((decodeList c).map (Nat.pair n ·)).reverse := by
  unfold mapPairCode
  rw [foldCode_eq']
  have h := decodeList_foldl_mapPairStp n (decodeList c) 0
  rwa [decodeList_zero, List.append_nil] at h

end Domain.Recursive
