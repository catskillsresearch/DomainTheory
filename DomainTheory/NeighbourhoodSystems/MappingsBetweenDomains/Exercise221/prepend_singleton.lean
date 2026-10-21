/-ai
Prepending a finite binary string σ to the singleton of a finite binary string ρ yields the singleton of σ followed by ρ.

By extensionality, a string in the prepend is σ followed by ρ, and σ followed by ρ arises by taking ρ from the singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `σ{ρ} = {σρ}`: prepending `σ` to a terminator singleton. -/
theorem prepend_singleton (σ ρ : Str) : prepend σ ({ρ} : Set Str) = ({σ ++ ρ} : Set Str) := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨τ, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨ρ, rfl, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
