module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

def sexprToNat : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (Encodable.encode σ)
  | .cat a b => Nat.pair 2 (Nat.pair (sexprToNat a) (sexprToNat b))
  | .cap a b => Nat.pair 3 (Nat.pair (sexprToNat a) (sexprToNat b))

end Exercise722

end DomainTheory.NeighbourhoodSystems
