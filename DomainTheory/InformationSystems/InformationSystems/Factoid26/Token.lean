/-ai
A token for partial maps from a set A to a set B is either the least-informative object or a graph atom pairing an element of A with an element of B. Equality of these tokens is decidable.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- Tokens: `bot` ≃ `Δ`, or a graph atom `pair a b`. -/
inductive Token (A B : Type*) where
  | bot
  | pair (a : A) (b : B)
  deriving DecidableEq

end Factoid26
end DomainTheory.InformationSystems
