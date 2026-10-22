/-ai
sexprOfNat decodes a natural number as an optional expression by running the fuel-bounded decoder at that number with fuel one greater than the number.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

def sexprOfNat (n : ℕ) : Option SExpr := sexprOfNatFuel (n + 1) n

end Exercise722

end DomainTheory.NeighbourhoodSystems
