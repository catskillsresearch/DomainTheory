/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem85.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}





/-- **Principal elements are compact**: if `↑X ⊑ ⋃ᵢ dᵢ` for a directed family, then already
`↑X ⊑ dᵢ` for some single `i`. Immediate from `X ∈ ↑X` and `mem_iSupDirected`. -/
theorem principal_compact {X : Set γ} (hX : V.mem X) {I : Type*} [Nonempty I]
    (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
    (h : V.principal hX ≤ iSupDirected d hdir) : ∃ i, V.principal hX ≤ d i := by
  obtain ⟨i, hi⟩ := (mem_iSupDirected d hdir).mp (h X ⟨hX, subset_rfl⟩)
  exact ⟨i, fun _ ⟨hW, hXW⟩ => (d i).up_mem hi hW hXW⟩

end Algebraic
end DomainTheory.Neighborhood
