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
import DomainTheory.Neighborhood.Recursive.getD_append_cf
import DomainTheory.Neighborhood.Recursive.getD_append_right_cf


namespace Domain.Recursive





































































































































































































































theorem appendListCode_eq (c1 c2 : ℕ) :
    decodeList (appendListCode c1 c2) = decodeList c1 ++ decodeList c2 := by
  unfold appendListCode
  rw [decodeList_tabCode, listLenChar_eq c1, listLenChar_eq c2]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < (decodeList c1).length + (decodeList c2).length
  · have hf := appendListTabFn_eq c1 c2 (decodeList c1).length i
    rw [getD_map_range_cf
        (fun j => appendListTabFn (Nat.pair j (Nat.pair c1 (Nat.pair c2 (decodeList c1).length)))) d hi,
      hf]
    by_cases hlt : i < (decodeList c1).length
    · rw [ite_eq_left hlt,
        show (decodeList c1).getD i 0 = (decodeList c1).getD i d from by
          rw [getD_eq_getElem_cf _ 0 hlt, getD_eq_getElem_cf _ d hlt],
        (getD_append_cf (decodeList c1) (decodeList c2) d hlt).symm]
    · rw [ite_eq_right hlt,
        show (decodeList c2).getD (i - (decodeList c1).length) 0 =
            (decodeList c2).getD (i - (decodeList c1).length) d from by
          have hi2 : i - (decodeList c1).length < (decodeList c2).length := by
            have hle : (decodeList c1).length ≤ i := Nat.le_of_not_gt hlt
            omega
          rw [getD_eq_getElem_cf _ 0 hi2, getD_eq_getElem_cf _ d hi2],
        (getD_append_right_cf (decodeList c1) (decodeList c2) d (Nat.le_of_not_gt hlt)).symm]
  · have hge : (decodeList c1).length + (decodeList c2).length ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_append]; exact hge)]

end Domain.Recursive
