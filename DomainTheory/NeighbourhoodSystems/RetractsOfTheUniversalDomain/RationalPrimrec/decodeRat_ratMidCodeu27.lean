module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_ratMidCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


/-- **`decodeRat_ratMidCode`, un-paired**: lets callers apply it to an arbitrary code `e`
(typically itself obtained by decoding a list, e.g. `firstElemCode`) without first having to
rewrite `e` as `Nat.pair e.unpair.1 e.unpair.2` in the ambient goal — doing that rewrite directly
on a term still containing `e` risks the `whnf`-blowup this project has hit before whenever `e`
is (or unfolds to) a large composite expression. -/
theorem decodeRat_ratMidCode' (e : ℕ) :
    decodeRat (ratMidCode e) = (decodeRat e.unpair.1 + decodeRat e.unpair.2) / 2 := by
  have h := decodeRat_ratMidCode e.unpair.1 e.unpair.2
  rwa [Nat.pair_unpair] at h

end DomainTheory.NeighbourhoodSystems
