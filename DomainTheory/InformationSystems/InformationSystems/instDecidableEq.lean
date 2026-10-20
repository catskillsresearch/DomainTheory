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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

namespace Token

/-- Decidable equality ignores the `<` proof (proof-irrelevant). -/
instance instDecidableEq : DecidableEq Token
  | bot, bot => isTrue rfl
  | bot, interval _ _ _ => isFalse Token.noConfusion
  | interval _ _ _, bot => isFalse Token.noConfusion
  | interval n m _, interval n' m' _ =>
    if h : n = n' ∧ m = m' then
      isTrue (by
        rcases h with ⟨rfl, rfl⟩
        rfl)
    else
      isFalse (by
        intro hEq
        injection hEq with hn hm
        exact h ⟨hn, hm⟩)

end Token

end Factoid25

end DomainTheory.InformationSystems
