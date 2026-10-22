module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem qpNonemptyBop_eq_one_iff (e : ℕ) :
    qpNonemptyBop e = 1 ↔ (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyBop decodeRatPair; exact ratLtCode_eq_one_iff e.unpair.1 e.unpair.2

end DomainTheory.NeighbourhoodSystems
