/-ai
The singleton of a finite binary string σ and the cone of a finite binary string τ are nested or disjoint.

If τ is a prefix of σ, the singleton is contained in the cone. Otherwise the intersection is empty, because a common element would equal σ and would have τ as a prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for a terminator singleton vs. a cone (the mirror of `cone_singleton_nd`). -/
theorem singleton_cone_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ cone τ ∨ cone τ ⊆ ({σ} : Set Str) ∨ ({σ} : Set Str) ∩ cone τ = ∅ :=
  if h : τ <+: σ then
    Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl hw
      exact h hw))

end DomainTheory.NeighbourhoodSystems.Exercise221
