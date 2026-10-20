module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive
















































theorem Lenum_subset_char_eq_one_iff (n m : ℕ) :
    Lenum n ⊆ Lenum m ↔ LenumSubsetChar (Nat.pair n m) = 1 := by
  unfold LenumSubsetChar
  rw [unpair_pair_fst, unpair_pair_snd, Lenum_subset_iff]

end DomainTheory.NeighbourhoodSystems.Exercise724
