module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ComputableBisection

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

def UBisection2 : ComputableBisection UComputablePresentation where
  left := splitU2Left
  right := splitU2Right
  left_primrec := primrec.splitU2Left
  right_primrec := primrec.splitU2Right
  disjoint := splitU2.disjoint
  union := splitU2.union
  left_congr := fun _ _ h => splitU2Left_congr h
  right_congr := fun _ _ h => splitU2Right_congr h

end DomainTheory.NeighbourhoodSystems
