/-ai
The negative numerator part of a rational code is primitive recursive.

It is the right component of the left component of the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive













theorem primrec_qNumN : Nat.Primrec qNumN := Nat.Primrec.right.comp Nat.Primrec.left
end DomainTheory.NeighbourhoodSystems
