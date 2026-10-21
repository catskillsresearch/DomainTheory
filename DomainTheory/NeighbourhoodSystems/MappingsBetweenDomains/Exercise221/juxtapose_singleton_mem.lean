/-ai
A set Z belongs to the juxtaposition of the total finite sequence σ with an element y if and only if Z is a neighbourhood of the system C and Z contains the prepend of σ to some neighbourhood of y.

If Z belongs to the juxtaposition, the witnessing first neighbourhood is contained in the singleton of σ. When it is a cone of a string ρ, ρ is a prefix of σ, and the master neighbourhood of y prepends to the cone of σ, which is contained in the cone of ρ and hence in Z. When it is a singleton of ρ, that string equals σ and the witnessing second neighbourhood is the required one. Conversely, the singleton of σ together with the given neighbourhood of y witnesses the singleton disjunct of the relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`σy` for a total finite `x = ↑{σ}`.** When the first argument is the total finite sequence
`σ`, juxtaposition prepends `σ` to `y`: `Z ∈ (↑{σ})y` iff `Z` contains `σY'` for some `Y' ∈ y`. The
coarser cone witnesses `σΣ* ∈ ↑{σ}` add nothing, since `σΔ = σΣ*` is itself of the form `σY'`. -/
theorem juxtapose_singleton_mem (σ : Str) (y : C.Element) {Z : Set Str} :
    (juxtapose.toElementMap₂ (singletonElt σ) y).mem Z ↔
      C.mem Z ∧ ∃ Y', y.mem Y' ∧ prepend σ Y' ⊆ Z := by
  constructor
  · rintro ⟨X, Y, ⟨_, hsingleX⟩, hYmem, _, hZ, hd⟩
    refine ⟨hZ, ?_⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, hsub⟩
    · have hρσ : ρ <+: σ := mem_cone.mp (Set.singleton_subset_iff.mp hsingleX)
      refine ⟨C.master, y.master_mem, ?_⟩
      rw [C_master, prepend_univ]
      exact (cone_subset_cone.mpr hρσ).trans hsub
    · obtain rfl : σ = ρ := by
        have := Set.singleton_subset_iff.mp hsingleX
        rwa [Set.mem_singleton_iff] at this
      exact ⟨Y, hYmem, hsub⟩
  · rintro ⟨hZ, Y', hY'mem, hsub⟩
    exact ⟨{σ}, Y', ⟨memC_singleton σ, subset_rfl⟩, hY'mem, y.sub hY'mem, hZ,
      Or.inr ⟨σ, rfl, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
