module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singletonElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Lambda
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.juxtapose
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_not_subset_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_cone_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.nestedOrDisjoint_C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.subset_singleton_eq
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_prepend
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_subset_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`⊥ ⊏ Λ`.** The undefined sequence `⊥ = ↑Δ` is strictly below the total empty sequence
`Λ = ↑{[]}`: they are distinct because `⊥` contains only `Δ`, whereas `Λ` contains `{[]} ≠ Δ`. -/
theorem bot_lt_Lambda : C.bot < Lambda := by
  refine lt_of_le_of_ne (C.bot_le _) ?_
  intro h
  have hmem : C.bot.mem ({([] : Str)} : Set Str) := by
    rw [h]; exact ⟨memC_singleton [], subset_rfl⟩
  rw [C.mem_bot, C_master] at hmem
  have h2 : ([true] : Str) ∈ ({([] : Str)} : Set Str) := by rw [hmem]; trivial
  rw [Set.mem_singleton_iff] at h2
  exact absurd h2 (by decide)

end DomainTheory.NeighbourhoodSystems.Exercise221
