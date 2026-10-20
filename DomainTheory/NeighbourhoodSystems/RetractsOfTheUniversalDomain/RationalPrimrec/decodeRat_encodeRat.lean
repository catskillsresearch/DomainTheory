module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.encodeRat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

@[simp] theorem decodeRat_encodeRat (q : ℚ) : decodeRat (encodeRat q) = q := by
  unfold decodeRat encodeRat
  rw [unpair_pair, decodeInt_encodeInt]
  have hden : q.den - 1 + 1 = q.den := by
    have := q.den_nz; omega
  rw [hden, Rat.mkRat_self]

end DomainTheory.NeighbourhoodSystems
