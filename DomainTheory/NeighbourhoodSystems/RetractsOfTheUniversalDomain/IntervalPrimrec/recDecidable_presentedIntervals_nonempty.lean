module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.primrec_qpNonemptyChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyChar_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.presentedIntervals_decodeQPairList_nonempty_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








































/-- **Non-emptiness of the set presented by a QPair-list code is recursively decidable.** -/
theorem recDecidable_presentedIntervals_nonempty :
    RecDecidable (fun c => (presentedIntervals (decodeQPairList c)).Nonempty) :=
  RecDecidable.of_zero_one_char primrec_qpNonemptyChar
    (fun c => by have := qpNonemptyChar_le_one c; omega)
    presentedIntervals_decodeQPairList_nonempty_iff

end DomainTheory.NeighbourhoodSystems
