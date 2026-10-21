/-ai
The nonempty-presentation flag of a rational-pair list code is at most one.

It is the corresponding bound for the bounded existential characteristic, with the
unused parameter fixed at zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








































theorem qpNonemptyChar_le_one (c : ℕ) : qpNonemptyChar c ≤ 1 := existsListChar_le_one _ 0 c

end DomainTheory.NeighbourhoodSystems
