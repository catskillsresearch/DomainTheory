module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel_sexprToNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

instance : Encodable SExpr where
  encode := sexprToNat
  decode := sexprOfNat
  encodek e := sexprOfNatFuel_sexprToNat e (sexprToNat e + 1) (Nat.lt_succ_self _)

end Exercise722

end DomainTheory.NeighbourhoodSystems
