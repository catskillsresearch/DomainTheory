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











/-- **Characterization of `S` as the regular events of this fragment.** A language `X` is in `S`
exactly when it is the *non-empty* denotation of some `Σ`/`{σ}`/`·`/`∩` expression. This is the
precise content of Scott's "the sets in `S` are each regular events". -/
theorem inS_iff_exists_denote {X : Set (List Bool)} :
    InS X ↔ ∃ e : SExpr, denote e = X ∧ X.Nonempty := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, he, h.nonempty⟩
  · rintro ⟨e, rfl, hne⟩
    exact InS_denote_of_nonempty hne

end Exercise722
end DomainTheory.Neighborhood
