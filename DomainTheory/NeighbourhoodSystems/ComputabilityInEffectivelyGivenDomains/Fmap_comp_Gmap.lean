module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- `F ∘ G = I_{(D^∞)^∞}`. -/
theorem Fmap_comp_Gmap : (Fmap V).comp (Gmap V) = idMap (iterSys (iterSys V)) := by
  apply ApproximableMap.ext
  intro S S'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hS, hW, hg⟩, ⟨-, hS', hf⟩⟩
    refine ⟨hS, hS', subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))⟩
    show fiber2 S i j ⊆ fiber2 S' i j
    have h1 : fiber2 S i j ⊆ fiber W (Nat.pair i j) := by
      have := hg (Nat.pair i j)
      rwa [unpair_pair_fst, unpair_pair_snd] at this
    exact h1.trans (hf i j)
  · rintro ⟨hS, hS', hSS'⟩
    refine ⟨reindexG S, ⟨hS, reindexG_mem hS, ?_⟩, ⟨reindexG_mem hS, hS', ?_⟩⟩
    · intro k; rw [fiber_reindexG]
    · intro i j
      rw [fiber_reindexG, unpair_pair_fst, unpair_pair_snd]
      exact fiber2_mono hSS' i j

end Exercise718

end DomainTheory.NeighbourhoodSystems
