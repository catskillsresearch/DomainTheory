module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right_congr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U`'s computable canonical bisection, packaged as a `ComputableBisection`** — the missing
`(f)`-side prerequisite, fixing `SplitU.lean`'s `left_congr`/`right_congr` gap (see the module
docstring). -/
def UBisection2 : ComputableBisection UComputablePresentation where
  left := splitU2Left
  right := splitU2Right
  left_primrec := primrec_splitU2Left
  right_primrec := primrec_splitU2Right
  disjoint := splitU2_disjoint
  union := splitU2_union
  left_congr := fun _ _ h => splitU2Left_congr h
  right_congr := fun _ _ h => splitU2Right_congr h

end DomainTheory.NeighbourhoodSystems
