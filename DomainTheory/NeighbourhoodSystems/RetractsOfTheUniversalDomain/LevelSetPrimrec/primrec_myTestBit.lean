/-ai
The bit test is primitive recursive. On a paired code it is the residue modulo 2 of the iterated division of the first component by two to the power of the second.

The residue modulo 2, composed with the primitive-recursive iterated division, is primitive recursive, and it agrees with the bit test by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myDivPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myTestBit : Nat.Primrec (fun t => myTestBit t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp primrec_myDivPow2).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
