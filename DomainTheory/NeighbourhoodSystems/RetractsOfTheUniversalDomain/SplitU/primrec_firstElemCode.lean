/-ai
firstElemCode is primitive recursive.

It is the left projection composed with the predecessor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem












theorem primrec_firstElemCode : Nat.Primrec firstElemCode :=
  Nat.Primrec.left.comp primrec_pred

end DomainTheory.NeighbourhoodSystems
