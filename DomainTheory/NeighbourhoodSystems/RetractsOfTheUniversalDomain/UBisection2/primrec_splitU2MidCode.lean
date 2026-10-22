module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_splitU2MidCode : Nat.Primrec splitU2MidCode :=
  (primrec_ratMidCode.comp
    ((primrec_listMinFstCode.comp primrec_canonCode).pair
      (primrec_listMaxSndCode.comp primrec_canonCode))).of_eq fun n => by
    simp only [splitU2MidCode]

end DomainTheory.NeighbourhoodSystems
