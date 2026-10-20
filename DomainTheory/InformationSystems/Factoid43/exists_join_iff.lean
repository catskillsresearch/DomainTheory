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
import DomainTheory.InformationSystems.Factoid43.le_join_left
import DomainTheory.InformationSystems.Factoid43.le_join_right


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)







/-- Binary join exists iff some element bounds both. -/
theorem exists_join_iff (x y : sys.Element) :
    (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
      Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) := by
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨fun Y hY => z.consistent Y (fun a ha => by
      rcases hY ha with h | h
      · exact hx h
      · exact hy h)⟩
  · rintro ⟨h⟩
    exact ⟨sys.join x y h, sys.le_join_left x y h, sys.le_join_right x y h⟩

end InfoSys
end DomainTheory.InformationSystems
