/-ai
A token is either the least-informative object, read as the unbounded interval from 0 to infinity, or a strict integer interval whose lower endpoint is strictly below its upper endpoint.
ai-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Tokens: `bot` ≃ `(0, ∞)`, or a strict integer interval `(lo, hi)`. -/
inductive Token : Type where
  | bot
  | interval (lo hi : ℕ) (hlt : lo < hi)

end Factoid25
end DomainTheory.InformationSystems
