/-ai
The presentation-independent midpoint code is primitive recursive.

Compose the primitive-recursive rational midpoint with the pair of the minimum-first code and the maximum-second code, each composed with the canonical code, and identify the result with the midpoint code by its definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_splitU2MidCode : Nat.Primrec splitU2MidCode :=
  (primrec_ratMidCode.comp
    ((primrec_listMinFstCode.comp primrec_canonCode).pair
      (primrec_listMaxSndCode.comp primrec_canonCode))).of_eq fun n => by
    simp only [splitU2MidCode]

end DomainTheory.NeighbourhoodSystems
