/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Proposition56
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid65.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


/-- The unique element of `|1|` is `⊥`. -/
theorem unitElement_eq_bot (x : unitSystem.Element) : x = unitSystem.botElement := by
  apply le_antisymm
  · intro a ha
    cases a
    exact trivial
  · exact botElement_le unitSystem x

end InfoSys
end DomainTheory.InformationSystems
