/-ai
splitMidCode is primitive recursive.

It is the rational midpoint code composed with the first-element code composed with the canonical code, and that composite agrees with the midpoint code by simplification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.primrec_firstElemCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem














theorem primrec_splitMidCode : Nat.Primrec splitMidCode :=
  (primrec_ratMidCode.comp (primrec_firstElemCode.comp primrec_canonCode)).of_eq fun n => by
    simp only [splitMidCode]

end DomainTheory.NeighbourhoodSystems
