module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_splitU2Right : Nat.Primrec splitU2Right :=
  (primrec_clipGeListCode.comp (primrec_splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitU2Right, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
