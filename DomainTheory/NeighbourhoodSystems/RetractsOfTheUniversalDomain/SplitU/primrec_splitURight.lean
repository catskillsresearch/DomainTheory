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
