/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Exercise221.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise221

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB


















/-- **Total finite sequences.** `↑{σ}` is a total (maximal) element of `|𝒞|`: any element above it
must equal it, because `{σ}` is a minimal nonempty neighbourhood. This is what was *false* in `𝔹`,
where finite sequences gave only the partial `σ⊥`. -/
theorem isTotal_singletonElt (σ : Str) : C.IsTotal (singletonElt σ) := by
  intro y hy Z hZ
  have hσy : y.mem ({σ} : Set Str) := hy {σ} ⟨memC_singleton σ, subset_rfl⟩
  have hinter : y.mem (({σ} : Set Str) ∩ Z) := y.inter_mem hσy hZ
  have hmemC : C.mem (({σ} : Set Str) ∩ Z) := y.sub hinter
  have heq : ({σ} : Set Str) ∩ Z = ({σ} : Set Str) :=
    subset_singleton_eq hmemC Set.inter_subset_left
  exact ⟨y.sub hZ, by rw [← heq]; exact Set.inter_subset_right⟩

end DomainTheory.Neighborhood.Exercise221
