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
