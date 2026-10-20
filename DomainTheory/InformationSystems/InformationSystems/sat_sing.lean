module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.Sat
public import DomainTheory.InformationSystems.InformationSystems.sat_midpoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Every token is satisfiable. -/
theorem sat_sing (t : Token) : ∃ x : ℚ, Sat x t := by
  cases t with
  | bot => exact ⟨0, trivial⟩
  | interval lo hi hlt => exact ⟨_, sat_midpoint hlt⟩

end Factoid25

end DomainTheory.InformationSystems
