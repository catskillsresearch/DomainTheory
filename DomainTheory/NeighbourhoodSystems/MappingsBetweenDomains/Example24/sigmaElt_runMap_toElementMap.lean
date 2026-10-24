module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap_toElementMap_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The "shift formula" for `runMap` (output side).** Since `g(x)`'s membership predicate is
itself a cone-monotone family (`runMap_toElementMap_mem`), prepending `τ₀` to `g(x)` collapses the
same way: the up-closure of neighbourhoods `Z ⊇ (out τ)Σ*` is absorbed because `(out τ)Σ*` itself
is the *deepest* (hence hardest-to-satisfy, so witness-minimal) choice. -/
theorem sigmaElt_runMap_toElementMap (τ₀ : Str) (x : B.Element) (Y : Set Str) :
    (sigmaElt τ₀ (runMap.toElementMap x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (τ₀ ++ out τ) ⊆ Y := by
  constructor
  · rintro ⟨hYmem, Z, hZ, hsub⟩
    obtain ⟨τ, hτ, _, hZsub⟩ := (runMap_toElementMap_mem x Z).mp hZ
    refine ⟨τ, hτ, hYmem, ?_⟩
    rw [← prepend_cone]
    exact (prepend_mono τ₀ hZsub).trans hsub
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    refine ⟨hYmem, cone (out τ),
      (runMap_toElementMap_mem x _).mpr ⟨τ, hτ, memB_cone _, subset_rfl⟩, ?_⟩
    rw [prepend_cone]
    exact hsub

end DomainTheory.NeighbourhoodSystems.Example24
