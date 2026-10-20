/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid42
import DomainTheory.InformationSystems.Factoid43.Basic
import DomainTheory.InformationSystems.Factoid43.le_familySup
import DomainTheory.InformationSystems.Factoid43.familySup_le
import DomainTheory.InformationSystems.Factoid43.finitelyConsistent_of_upperBound


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)






/-- Join exists iff the union is finitely consistent. -/
theorem exists_isLUB_iff (S : Set sys.Element) :
    (∃ z : sys.Element, (∀ x ∈ S, x ≤ z) ∧ ∀ w, (∀ x ∈ S, x ≤ w) → z ≤ w) ↔
      Nonempty (sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) := by
  constructor
  · rintro ⟨z, hub, _⟩
    exact ⟨sys.finitelyConsistent_of_upperBound S hub⟩
  · rintro ⟨hU⟩
    refine ⟨sys.familySup S hU, fun x hx => sys.le_familySup S hU hx,
      fun w hw => sys.familySup_le S hU hw⟩

end InfoSys
end DomainTheory.InformationSystems
