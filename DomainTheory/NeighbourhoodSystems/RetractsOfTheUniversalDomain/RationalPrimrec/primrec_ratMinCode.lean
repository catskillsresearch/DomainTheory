module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_ratLeCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive



















theorem primrec_ratMinCode : Nat.Primrec ratMinCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.left Nat.Primrec.right

end DomainTheory.NeighbourhoodSystems
