/-ai
splitURight is primitive recursive.

It is the upward list clip composed with the pairing of the midpoint code and the canonical code, and that composite agrees with the right half after the unpair-pair identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.primrec_clipGeListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.primrec_splitMidCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem
















theorem primrec_splitURight : Nat.Primrec splitURight :=
  (primrec_clipGeListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitURight, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
