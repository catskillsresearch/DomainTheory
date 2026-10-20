module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_ratLeCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive



















theorem primrec_ratMaxCode : Nat.Primrec ratMaxCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.right Nat.Primrec.left

end DomainTheory.NeighbourhoodSystems
