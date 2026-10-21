/-ai
The nonempty-presentation flag of a rational-pair list code equals one if and only if
some code in the decoded list decodes to a pair whose first component is strictly less
than its second.

Unfolding the flag and rewriting by the characterization of the bounded existential
characteristic, the existential is congruent in its right conjunct. The left pairing
projection and the characterization of the pair nonemptiness flag turn that conjunct
into the comparison of the decoded components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyBop_eq_one_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








































theorem qpNonemptyChar_eq_one_iff (c : ℕ) :
    qpNonemptyChar c = 1 ↔ ∃ e ∈ decodeList c, (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyChar
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [unpair_pair_fst, qpNonemptyBop_eq_one_iff]

end DomainTheory.NeighbourhoodSystems
