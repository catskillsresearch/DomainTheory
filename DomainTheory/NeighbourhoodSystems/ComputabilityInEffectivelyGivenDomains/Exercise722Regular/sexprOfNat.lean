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
