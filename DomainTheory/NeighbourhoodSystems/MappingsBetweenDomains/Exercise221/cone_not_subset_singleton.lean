/-ai
The cone of a finite binary string σ is never contained in the singleton of a finite binary string τ.

If it were, both σ and the string formed by appending false to σ would lie in the singleton, hence both would equal τ and therefore each other. Comparing lengths, the appended string is longer by one, which is impossible.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- A singleton is never a cone (a cone has at least two elements `σ` and `σ0`). -/
theorem cone_not_subset_singleton (σ τ : Str) : ¬ cone σ ⊆ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ ({τ} : Set Str) := h (mem_cone.mpr List.prefix_rfl)
  have h2 : (σ ++ [false]) ∈ ({τ} : Set Str) := h (mem_cone.mpr (List.prefix_append σ [false]))
  rw [Set.mem_singleton_iff] at h1 h2
  rw [← h1] at h2
  have hlen := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end DomainTheory.NeighbourhoodSystems.Exercise221
