module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

inductive Token : Type where
  | bot
  | interval (lo hi : ℕ) (hlt : lo < hi)

end DomainTheory.InformationSystems
