/-ai
The encoding instance for expressions encodes by sexprToNat and decodes by sexprOfNat. The round trip decodes the code with fuel one greater than the code, which the fuel lemma and the successor bound show returns the original expression.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel_sexprToNat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

instance : Encodable SExpr where
  encode := sexprToNat
  decode := sexprOfNat
  encodek e := sexprOfNatFuel_sexprToNat e (sexprToNat e + 1) (Nat.lt_succ_self _)

end Exercise722

end DomainTheory.NeighbourhoodSystems
