/-ai
The map sexprToNat sends a symbolic expression to a natural number by pairing a constructor tag with its payload. The constant sigma is sent to the pair of 0 and 0. A singleton letter is sent to the pair of 1 and the encoding of that letter. Concatenation is sent to the pair of 2 and the pair of the recursively encoded arguments, and intersection is sent to the pair of 3 and the pair of the recursively encoded arguments.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

def sexprToNat : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (Encodable.encode σ)
  | .cat a b => Nat.pair 2 (Nat.pair (sexprToNat a) (sexprToNat b))
  | .cap a b => Nat.pair 3 (Nat.pair (sexprToNat a) (sexprToNat b))

end Exercise722

end DomainTheory.NeighbourhoodSystems
