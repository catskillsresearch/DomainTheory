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


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)







theorem join_le (x y z : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier))
    (hx : x ≤ z) (hy : y ≤ z) : sys.join x y h ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    rcases huU hb with hb' | hb'
    · exact hx hb'
    · exact hy hb'
  exact z.closed u a huZ hEnt

end InfoSys
end DomainTheory.InformationSystems
