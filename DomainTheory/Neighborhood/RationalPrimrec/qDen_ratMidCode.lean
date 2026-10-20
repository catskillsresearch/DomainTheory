/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RationalPrimrec.Basic
import DomainTheory.Neighborhood.RationalPrimrec.qDen_pos


namespace DomainTheory.Neighborhood

open Domain.Recursive

























theorem qDen_ratMidCode (c1 c2 : ℕ) : qDen (ratMidCode (Nat.pair c1 c2)) = qDen c1 * qDen c2 * 2 := by
  have h1 : 1 ≤ 2 * qDen c1 * qDen c2 := by
    have hd1 := qDen_pos c1
    have hd2 := qDen_pos c2
    have : 0 < 2 * qDen c1 * qDen c2 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hd2
    omega
  show (ratMidCode (Nat.pair c1 c2)).unpair.2 + 1 = qDen c1 * qDen c2 * 2
  simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [Nat.sub_add_cancel h1]; ring

end DomainTheory.Neighborhood
