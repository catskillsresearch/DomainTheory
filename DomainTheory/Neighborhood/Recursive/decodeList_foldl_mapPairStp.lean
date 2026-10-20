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
import DomainTheory.Neighborhood.Recursive.mapPairStp_eq
import DomainTheory.Neighborhood.Recursive.decodeList_mapPairStep


namespace Domain.Recursive


























































































































theorem decodeList_foldl_mapPairStp (n : ℕ) (el : List ℕ) (acc : ℕ) :
    decodeList (List.foldl (fun acc x => mapPairStp (Nat.pair x (Nat.pair acc n))) acc el)
      = (el.map (Nat.pair n ·)).reverse ++ decodeList acc := by
  induction el generalizing acc with
  | nil => simp
  | cons e el ih =>
    rw [List.foldl_cons, ih, mapPairStp_eq, decodeList_mapPairStep, List.map_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]

end Domain.Recursive
