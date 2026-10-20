module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
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
