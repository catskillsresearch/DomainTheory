/-ai
The inverse reindexing map composed with the forward reindexing map is the identity on the iterated neighbourhood system.

By extensionality of approximable maps, a composite witness supplies an intermediate neighbourhood whose double fibers sit between the fibers, so after pairing an unpairing the first neighbourhood is contained in the second. Conversely, if the first neighbourhood is contained in the second, its reindexing along pairing is an intermediate neighbourhood: its double fibers recover the fibers, and the inverse inclusions are monotonicity of fibers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_mem
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

/-- `G ∘ F = I_{D^∞}`. -/
theorem Gmap_comp_Fmap : (Gmap V).comp (Fmap V) = idMap (iterSys V) := by
  apply ApproximableMap.ext
  intro W W'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨S, ⟨hW, hS, hf⟩, ⟨-, hW', hg⟩⟩
    refine ⟨hW, hW', subset_of_fiber_subset (fun k => ?_)⟩
    have h1 : fiber W k ⊆ fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := by
      have := hf (Nat.unpair k).1 (Nat.unpair k).2
      rwa [pair_unpair] at this
    exact h1.trans (hg k)
  · rintro ⟨hW, hW', hWW'⟩
    refine ⟨reindexF W, ⟨hW, reindexF_mem hW, ?_⟩, ⟨reindexF_mem hW, hW', ?_⟩⟩
    · intro i j; rw [fiber2_reindexF]
    · intro k
      rw [fiber2_reindexF, pair_unpair]
      exact fiber_mono hWW' k

end Exercise718

end DomainTheory.NeighbourhoodSystems
