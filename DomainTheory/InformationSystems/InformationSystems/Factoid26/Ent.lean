/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- Minimal entailment, with LHS consistency baked in (Scott types `⊢` on `Con`). -/
def Ent {A B : Type*} (u : Finset (Token A B)) (X : Token A B) : Prop :=
  Consistent u ∧ (X = Token.bot ∨ X ∈ u)

end Factoid26

end DomainTheory.InformationSystems
