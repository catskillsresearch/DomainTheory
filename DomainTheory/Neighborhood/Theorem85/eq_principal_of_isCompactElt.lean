/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem85.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}






/-- **Compact elements are principal** — the converse of `principal_isCompactElt`, via
algebraicity: test compactness against `x`'s own principal-approximant family. -/
theorem eq_principal_of_isCompactElt {x : V.Element} (hx : IsCompactElt x) :
    ∃ (X : Set γ) (hX : V.mem X), x = V.principal hX := by
  have hle : x ≤ iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := le_of_eq (eq_iSupDirected_principal x)
  obtain ⟨i0, hi0⟩ :=
    hx (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2)) (principalFamily_directed x) hle
  exact ⟨i0.1, x.sub i0.2, le_antisymm hi0 (principal_le_of_mem i0.2)⟩

end Algebraic
end DomainTheory.Neighborhood
