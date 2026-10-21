/-ai
The element determined by an infinite sequence has no minimum neighbourhood. Any neighbourhood in the filter contains a prefix neighbourhood, and the next prefix neighbourhood is still in the filter and strictly smaller.

Suppose a neighbourhood contains the prefix neighbourhood of length n and is contained in every member. The prefix neighbourhood of length n + 1 is a member, so the supposed minimum is contained in it. With the shrinking of prefix neighbourhoods the two prefix neighbourhoods are equal, so their lists are equal by injectivity of the neighbourhood map, and the lengths n and n + 1 agree, which is impossible.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_length
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_finPrefix_antitone
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **The infinite elements have no minimum neighbourhood.** Given any witness `X ⊇ nbhd
(finPrefix f n)` in the filter, the *next* prefix neighbourhood is strictly smaller yet still in
the filter, so `X` cannot be the minimum. -/
theorem streamElement_not_hasMin (f : ℕ → ℕ) : ¬ HasMin (streamElement f) := by
  rintro ⟨X, ⟨-, n, hXsub⟩, hmin⟩
  have hmemsucc : (streamElement f).mem (nbhd (finPrefix f (n + 1))) := ⟨mem_nbhd _, n + 1, subset_rfl⟩
  have hle : X ⊆ nbhd (finPrefix f (n + 1)) := hmin _ hmemsucc
  have heq : nbhd (finPrefix f n) = nbhd (finPrefix f (n + 1)) :=
    Set.Subset.antisymm (hXsub.trans hle) (nbhd_finPrefix_antitone f (Nat.le_succ n))
  have hlen := congrArg List.length (nbhd_injective heq)
  rw [finPrefix_length, finPrefix_length] at hlen
  omega

end DomainTheory.NeighbourhoodSystems.Exercise724
