module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.mem_decodeQPairList_firstElemCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

















/-- The first pair `p₀` of `canonCode n`'s presenting list is non-degenerate, `p₀.1 < p₀.2`. -/
theorem splitU_p0_lt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < (decodeRatPair (firstElemCode (canonCode n))).2 :=
  forall_lt_decodeQPairList_canonCode n _
    (mem_decodeQPairList_firstElemCode (canonCode_ne_zero n))

end DomainTheory.NeighbourhoodSystems
