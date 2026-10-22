module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_qDen : Nat.Primrec qDen :=
  Nat.Primrec.succ.comp Nat.Primrec.right

end DomainTheory.NeighbourhoodSystems
