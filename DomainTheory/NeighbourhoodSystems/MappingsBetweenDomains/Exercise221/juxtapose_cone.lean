/-ai
Juxtaposition of the principal element on the cone of a finite binary string σ with any second element is again that principal element.

Compare membership of a set Z. If Z belongs to the juxtaposition, the witnessing first neighbourhood is contained in the cone of σ, so it cannot be a singleton and must be a cone contained in Z. Conversely, if the cone of σ is contained in a neighbourhood Z, that cone, the master neighbourhood, and the cone disjunct of the relation witness membership of Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

























/-- **Left-to-right bias / "`x` infinite ⟹ `xy = x`".** On a partial input `σ⊥ = ↑(σΣ*)` the
juxtaposition returns `σ⊥` itself, *independently of `y`*. Since an infinite (total) sequence is the
directed union of its finite approximants `σ⊥`, this says `xy = x` for total infinite `x`. -/
theorem juxtapose_cone (σ : Str) (y : C.Element) :
    juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y = C.principal (memC_cone σ) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, ⟨_, hconeX⟩, _, hY, hZ, hd⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, _⟩
    · exact ⟨hZ, hconeX.trans hsub⟩
    · exact absurd hconeX (cone_not_subset_singleton σ ρ)
  · rintro ⟨hZ, hconeσZ⟩
    exact ⟨cone σ, C.master, ⟨memC_cone σ, subset_rfl⟩, y.master_mem, C.master_mem, hZ,
      Or.inl ⟨σ, rfl, hconeσZ⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
