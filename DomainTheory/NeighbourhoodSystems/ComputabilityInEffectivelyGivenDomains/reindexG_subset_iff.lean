module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem reindexG_subset_iff {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    reindexG S ⊆ W ↔ ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := by
  constructor
  · intro h k
    have := fiber_mono h k
    rwa [fiber_reindexG] at this
  · intro h
    refine subset_of_fiber_subset (fun k => ?_)
    rw [fiber_reindexG]; exact h k

end Exercise718

end DomainTheory.NeighbourhoodSystems
