module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`B812e`: `V`'s computable canonical bisection, packaged as a `ComputableBisection`.** -/
def B812e : ComputableBisection VComputablePresentation where
  left := splitVLeft
  right := splitVRight
  left_primrec := primrec_splitVLeft
  right_primrec := primrec_splitVRight
  disjoint := splitV_disjoint
  union := splitV_union
  left_congr := fun _ _ h => splitVLeft_congr h
  right_congr := fun _ _ h => splitVRight_congr h

end DomainTheory.NeighbourhoodSystems
