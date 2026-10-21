/-ai
The bottom element of the system C is strictly below the total empty sequence.

The bottom element lies below every element, so it remains to show that the two elements differ. If they were equal, the singleton of the empty string would belong to the bottom element, and membership in the bottom element means equality with the master neighbourhood, the set of all strings. The one-bit string true would then belong to that singleton, so it would equal the empty string, which is absurd.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

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
