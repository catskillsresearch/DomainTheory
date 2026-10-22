module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_ratLeCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_ratLtCode : Nat.Primrec ratLtCode :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_ratLeCode.comp (Nat.Primrec.right.pair Nat.Primrec.left))

end DomainTheory.NeighbourhoodSystems
