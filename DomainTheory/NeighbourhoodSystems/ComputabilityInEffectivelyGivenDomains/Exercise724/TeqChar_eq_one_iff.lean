/-ai
The equality characteristic of two natural numbers equals 1 if and only if the two numbers are equal.

Unfold the characteristic and the zero test. The resulting numerical equivalence is arithmetic.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive


open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)


theorem TeqChar_eq_one_iff (a b : ℕ) : TeqChar a b = 1 ↔ a = b := by
  unfold TeqChar isZero; omega

end DomainTheory.NeighbourhoodSystems.Exercise724
