module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_qpNonemptyBop : Nat.Primrec qpNonemptyBop :=
  primrec_ratLtCode.comp (Nat.Primrec.left.pair Nat.Primrec.right)

end DomainTheory.NeighbourhoodSystems
