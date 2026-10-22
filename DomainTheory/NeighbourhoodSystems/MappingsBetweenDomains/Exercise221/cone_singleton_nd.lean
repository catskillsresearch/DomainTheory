module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for a cone vs. a terminator singleton: `{τ} ⊆ σΣ*` iff `σ ⪯ τ`, else
disjoint. Choice-free (`σ <+: τ` is decidable). -/
theorem cone_singleton_nd (σ τ : Str) :
    cone σ ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ cone σ ∨ cone σ ∩ ({τ} : Set Str) = ∅ :=
  if h : σ <+: τ then
    Or.inr (Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h)))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, mem_cone, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro hw rfl
      exact h hw))

end DomainTheory.NeighbourhoodSystems.Exercise221
