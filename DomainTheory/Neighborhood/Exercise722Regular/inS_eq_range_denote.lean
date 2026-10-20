/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722
import Mathlib.Logic.Encodable.Basic
import DomainTheory.Neighborhood.Exercise722Regular.Basic
import DomainTheory.Neighborhood.Exercise722Regular.InS_denote_of_nonempty
import DomainTheory.Neighborhood.Exercise722Regular.InS_exists_denote


namespace DomainTheory.Neighborhood

namespace Exercise722













theorem inS_eq_range_denote : {X | InS X} = denote '' {e | (denote e).Nonempty} := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, by rw [he]; exact h.nonempty, he⟩
  · rintro ⟨e, hne, rfl⟩
    exact InS_denote_of_nonempty hne

end Exercise722
end DomainTheory.Neighborhood
