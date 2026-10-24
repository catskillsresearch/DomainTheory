module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.PN
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.PNpres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem


/-- **Any two neighbourhoods of `PN` are consistent** (Scott: "any two neighbourhoods are
consistent"): their intersection `nbhd (n ||| m)` is itself a neighbourhood contained in both. -/
theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩

end DomainTheory.NeighbourhoodSystems.Example78
