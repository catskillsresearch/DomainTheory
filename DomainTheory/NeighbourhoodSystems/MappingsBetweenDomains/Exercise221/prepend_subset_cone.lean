/-ai
The prepend of a finite binary string σ to any set of strings is contained in the cone of σ.

An element of the prepend is σ followed by some string, so σ is a prefix of it and it belongs to the cone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `σY ⊆ σΣ* = cone σ`: prepending `σ` always lands inside the cone of `σ`. -/
theorem prepend_subset_cone (σ : Str) (Y : Set Str) : prepend σ Y ⊆ cone σ := by
  rintro w ⟨τ, _, rfl⟩
  exact mem_cone.mpr (List.prefix_append σ τ)

end DomainTheory.NeighbourhoodSystems.Exercise221
