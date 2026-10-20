/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.DAtomDecidable
import DomainTheory.Neighborhood.SplitU
import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.Theorem88b.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)







theorem hcover : ∀ S, D.mem S ↔ ∃ n, S = e P n := by
  intro S
  constructor
  · intro hS
    obtain ⟨n, hn⟩ := P.surj hS
    exact ⟨eIdx P n, by show S = P.X (eIdx P (eIdx P n)); rw [eIdx_involutive P n]; exact hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (P0 P).mem_X n

end DomainTheory.Neighborhood
