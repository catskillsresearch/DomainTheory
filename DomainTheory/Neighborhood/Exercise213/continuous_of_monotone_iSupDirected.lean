/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise122
import DomainTheory.Neighborhood.Exercise213.Basic
import DomainTheory.Neighborhood.Exercise213.principalFamily_directed
import DomainTheory.Neighborhood.Exercise213.eq_iSupDirected_principal


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem



/-- **The converse of `continuous_toElementMap`/`continuous_monotone`, in domain-theoretic form.**
A monotone function that also preserves directed unions is topologically continuous — the standard
"Scott continuity ⟺ order-theoretic continuity" bridge, proved directly from algebraicity rather
than through a general topological-basis argument: given `x ∈ c⁻¹U`, decompose `x` as the directed
union of its principal approximants (`eq_iSupDirected_principal`); `c` preserving the union puts
`c x` there too, so openness of `U` finds a witness `Y` in *some* `c(↑X)` (`X ∈ x`); monotonicity of
`c` then transfers `Y ∈ c(↑X)` up to every `x' ∈ [X]`, giving `[X] ⊆ c⁻¹U`. -/
theorem continuous_of_monotone_iSupDirected {c : V₀.Element → V₁.Element} (hmono : Monotone c)
    (hsup : ∀ {I : Type u} [Nonempty I] (d : I → V₀.Element)
      (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
      (hdir' : ∀ i j, ∃ k, c (d i) ≤ c (d k) ∧ c (d j) ≤ c (d k)),
      c (iSupDirected d hdir) = iSupDirected (fun i => c (d i)) hdir') :
    Continuous c := by
  rw [continuous_def]
  intro U hU x hx
  rw [Set.mem_preimage] at hx
  set fam : {X : Set α // x.mem X} → V₀.Element := fun i => V₀.principal (x.sub i.2) with hfam
  have hdir : ∀ i j : {X : Set α // x.mem X}, ∃ k, fam i ≤ fam k ∧ fam j ≤ fam k :=
    principalFamily_directed x
  have hdir' : ∀ i j : {X : Set α // x.mem X}, ∃ k, c (fam i) ≤ c (fam k) ∧ c (fam j) ≤ c (fam k) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hdir i j; exact ⟨k, hmono hik, hmono hjk⟩
  have hxeq : c x = iSupDirected (fun i => c (fam i)) hdir' :=
    (congrArg c (eq_iSupDirected_principal x)).trans
      (hsup (I := {X : Set α // x.mem X}) fam hdir hdir')
  rw [hxeq] at hx
  obtain ⟨Y, hY, hYU⟩ := hU _ hx
  obtain ⟨i, hi⟩ := (mem_iSupDirected _ hdir').mp hY
  refine ⟨i.1, i.2, fun x' hx' => hYU ?_⟩
  have hple : fam i ≤ x' := fun Z hZ => x'.up_mem hx' hZ.1 hZ.2
  exact (hmono hple) Y hi

end NeighborhoodSystem
end DomainTheory.Neighborhood
