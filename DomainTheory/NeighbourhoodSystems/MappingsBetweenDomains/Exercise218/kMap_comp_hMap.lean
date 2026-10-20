module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_hOut

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap















/-- **Exercise 2.18 — `k ∘ h = I_𝔹`.** The composite recovers the identity: reading `kOut (hOut σ) = σ`
through the cone relations. -/
theorem kMap_comp_hMap : kMap.comp hMap = idMap B := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨σ, hXcone, _, hYsub⟩, τ, hYcone, hZmem, hZsub⟩
    refine ⟨⟨σ, hXcone⟩, hZmem, ?_⟩
    have hτ : τ <+: hOut σ := cone_subset_cone.mp (hYcone ▸ hYsub)
    have hτσ : kOut τ <+: σ := by have := kOut_mono hτ; rwa [kOut_hOut] at this
    calc X = cone σ := hXcone
      _ ⊆ cone (kOut τ) := cone_subset_cone.mpr hτσ
      _ ⊆ Z := hZsub
  · rintro ⟨⟨σ, hXcone⟩, hZmem, hXZ⟩
    refine ⟨cone (hOut σ), ⟨σ, hXcone, memB_cone (hOut σ), subset_rfl⟩, hOut σ, rfl, hZmem, ?_⟩
    rw [kOut_hOut, hXcone] at *
    exact hXZ

end DomainTheory.NeighbourhoodSystems.Exercise218
