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
