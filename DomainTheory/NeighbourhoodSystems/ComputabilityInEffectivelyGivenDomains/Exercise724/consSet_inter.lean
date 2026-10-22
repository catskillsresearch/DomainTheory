module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Gamma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_injective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_consSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

theorem consSet_inter (i : ℕ) (X X' : Set Gamma) :
    consSet i X ∩ consSet i X' = consSet i (X ∩ X') := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet]
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, γ', hγ', heq⟩
    obtain ⟨-, hγγ'⟩ := cons_injective heq
    exact ⟨γ, ⟨hγ, hγγ' ▸ hγ'⟩, rfl⟩
  · rintro ⟨γ, ⟨hγ, hγ'⟩, rfl⟩
    exact ⟨⟨γ, hγ, rfl⟩, ⟨γ, hγ', rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
