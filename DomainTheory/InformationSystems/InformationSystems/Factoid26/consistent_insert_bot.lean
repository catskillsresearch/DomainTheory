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

theorem consistent_insert_bot {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (Token A B)} (hu : Consistent u) :
    Consistent (insert (Token.bot : Token A B) u) := by
  intro a b b' hb hb'
  have hb1 : Token.pair a b ∈ u := by
    rcases Finset.mem_insert.mp hb with h | h
    · cases h
    · exact h
  have hb2 : Token.pair a b' ∈ u := by
    rcases Finset.mem_insert.mp hb' with h | h
    · cases h
    · exact h
  exact hu hb1 hb2

end Factoid26

end DomainTheory.InformationSystems
