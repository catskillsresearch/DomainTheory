/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.InfoSys
import DomainTheory.InformationSystems.Factoid34.Basic


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




/-- **Factoid 3.4.** Top `⊤ = D` exists as an element iff every finite subset is consistent. -/
theorem exists_top_iff_allConsistent :
    (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent := by
  constructor
  · intro ⟨x, hx⟩ u
    exact x.consistent u (hx ▸ Set.subset_univ _)
  · intro h
    exact ⟨sys.topElement h, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
