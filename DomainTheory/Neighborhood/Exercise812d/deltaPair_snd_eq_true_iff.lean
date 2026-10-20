/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812c
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise718
import DomainTheory.Neighborhood.Exercise812d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


































theorem deltaPair_snd_eq_true_iff (k i : ℕ) : (deltaPair k i).2 = true ↔ (k / 4 ^ i / 2) % 2 = 1 := by
  unfold deltaPair; simp

end DomainTheory.Neighborhood
