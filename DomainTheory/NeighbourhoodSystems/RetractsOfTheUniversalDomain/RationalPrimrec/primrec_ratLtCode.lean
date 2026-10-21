/-ai
The strict rational comparison code is primitive recursive.

It is one minus the comparison code of the pair whose components have been exchanged, and exchanging the components is pairing the right component with the left.
ai-/
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
