module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.f
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.g
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T_nbhd_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_some
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_none
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_anti
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_agree
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.comparable_of_agree
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.prefix_of_encSet_subset

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 3.17 — `g` is a retraction of `f`.** `g ∘ f = I_B`. -/
theorem gf_eq_id : g.comp f = idMap B := by
  apply ApproximableMap.ext
  intro X Y
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨σ, hX, _, hσW⟩, _, τ, hY, hWτ⟩
    refine ⟨hX ▸ memB_cone σ, hY ▸ memB_cone τ, ?_⟩
    have hsub : encSet σ ⊆ encSet τ := hσW.trans hWτ
    rw [hX, hY]
    exact cone_subset_cone.mpr (prefix_of_encSet_subset hsub)
  · rintro ⟨hX, hY, hXY⟩
    obtain ⟨σ, rfl⟩ := hX
    obtain ⟨τ, rfl⟩ := hY
    have hpre : τ <+: σ := cone_subset_cone.mp hXY
    exact ⟨encSet σ, ⟨σ, rfl, encSet_mem σ, subset_rfl⟩,
      encSet_mem σ, τ, rfl, encSet_anti hpre⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
