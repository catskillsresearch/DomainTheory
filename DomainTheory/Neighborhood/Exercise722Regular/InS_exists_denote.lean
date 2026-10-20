/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722
import Mathlib.Logic.Encodable.Basic
import DomainTheory.Neighborhood.Exercise722Regular.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722











/-- **Completeness.** Every member of `S` is the denotation of some `S`-term. -/
theorem InS_exists_denote {X : Set (List Bool)} (h : InS X) : ∃ e : SExpr, denote e = X := by
  induction h with
  | univ => exact ⟨.sigma, rfl⟩
  | singleton σ => exact ⟨.single σ, rfl⟩
  | mul _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cat ea eb, rfl⟩
  | inter _ _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cap ea eb, rfl⟩

end Exercise722
end DomainTheory.Neighborhood
