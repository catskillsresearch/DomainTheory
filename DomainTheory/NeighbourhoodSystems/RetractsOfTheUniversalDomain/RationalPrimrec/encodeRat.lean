module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Encode a rational `q` using its own reduced `num`/`den`. -/
def encodeRat (q : ℚ) : ℕ := Nat.pair (encodeInt q.num) (q.den - 1)

end DomainTheory.NeighbourhoodSystems
