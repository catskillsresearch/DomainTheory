/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition710
import Mathlib.Tactic
import DomainTheory.Neighborhood.Definition711.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)









theorem PDmem_finJoin {n : ℕ} (xs : Fin n → V.Element) {W : Set (Set α)} :
    (V.PDfinJoin n xs).mem W ↔
      if n = 0 then W = V.PowerDomain.master else V.PDmemFinJoin xs W := by
  match n with
  | 0 => simp [PDfinJoin, PDfinJoinZero, mem_bot]
  | m + 1 => simp [PDfinJoin, PDfinJoinSucc]

end NeighborhoodSystem
end DomainTheory.Neighborhood
