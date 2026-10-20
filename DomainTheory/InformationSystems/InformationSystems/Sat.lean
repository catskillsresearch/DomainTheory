/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Satisfaction of a token at a rational point. -/
def Sat (x : ℚ) : Token → Prop
  | .bot => True
  | .interval lo hi _ => (lo : ℚ) < x ∧ x < (hi : ℚ)

end Factoid25

end DomainTheory.InformationSystems
