/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.presentedIntervals_map_qpClipGe
import DomainTheory.Neighborhood.SplitU.mem_decodeQPairList_clipGeListCode


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem










theorem presentedIntervals_decodeQPairList_clipGeListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipGeListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Ici (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipGe]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipGeListCode, List.mem_map]
  simp only [eq_comm]

end DomainTheory.Neighborhood
