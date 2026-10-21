/-ai
The body of the bounded search for a nonempty level set is primitive recursive. On a paired code it returns the bit test of the second component at the position given by the first component.

The bit test is primitive recursive, and so is its composition with the pairing of the right projection and the left projection. Unfolding the body and the two pairing identities shows that this composition is the body.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myTestBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_levelSetNonemptyBody : Nat.Primrec levelSetNonemptyBody :=
  (primrec_myTestBit.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
