module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive









/-- `decodeRat` is surjective: every rational number is `decodeRat` of some code (namely
`encodeRat q`). -/
theorem decodeRat_surjective : Function.Surjective decodeRat :=
  fun q => ⟨encodeRat q, decodeRat_encodeRat q⟩

end DomainTheory.NeighbourhoodSystems
