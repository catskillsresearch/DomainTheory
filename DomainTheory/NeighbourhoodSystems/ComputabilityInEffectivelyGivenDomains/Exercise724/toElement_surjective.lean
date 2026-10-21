/-ai
The map from finite or infinite sequences to elements of L is surjective. The infinite case chooses the witness stream by classical choice.

If the element has a minimum neighbourhood, that neighbourhood is the neighbourhood of a finite list and the element is the corresponding principal filter. If it has none, the stream extracted from the element is sent to it: a neighbourhood of the stream element contains a prefix neighbourhood of that stream, which lies in the element, so upward closure puts it in the element, and a neighbourhood of the element contains some finite prefix of the extracted stream.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toStream
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd_finPrefix_toStream
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_finPrefix_subset_of_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`toElement` is surjective** (Exercise 7.24, second claim, existence half; uses
`Classical.choice` via `buildData`/`toStream` for the infinite case — see `buildData`'s docstring).
-/
theorem toElement_surjective : Function.Surjective toElement := by
  intro x
  by_cases hx : HasMin x
  · obtain ⟨X, hXmem, hXmin⟩ := hx
    obtain ⟨l, rfl⟩ := x.sub hXmem
    exact ⟨Sum.inl l, (eq_principal_of_isMin (V := L) x hXmem hXmin).symm⟩
  · exact ⟨Sum.inr (toStream x hx), by
      apply Element.ext
      intro Z
      constructor
      · rintro ⟨hZmem, n, hn⟩
        exact x.up_mem (mem_nbhd_finPrefix_toStream x hx n) hZmem hn
      · intro hZ
        exact ⟨x.sub hZ, exists_finPrefix_subset_of_mem x hx hZ⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
