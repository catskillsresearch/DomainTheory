/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem







theorem decodeRatPair_clipLtCode (m e : ℕ) :
    decodeRatPair (clipLtCode (Nat.pair m e)) = qpClipLt (decodeRat m) (decodeRatPair e) := by
  unfold clipLtCode decodeRatPair qpClipLt
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMinCode]

end DomainTheory.Neighborhood
