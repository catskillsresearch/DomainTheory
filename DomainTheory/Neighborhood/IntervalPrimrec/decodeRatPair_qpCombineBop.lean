/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.RationalPrimrec
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.IntervalPrimrec.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive










theorem decodeRatPair_qpCombineBop (e1 e2 : ℕ) :
    decodeRatPair (qpCombineBop (Nat.pair e1 e2))
      = ((decodeRatPair e1).1 ⊔ (decodeRatPair e2).1, (decodeRatPair e1).2 ⊓ (decodeRatPair e2).2) := by
  unfold qpCombineBop decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode]

end DomainTheory.Neighborhood
