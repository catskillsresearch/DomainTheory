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






theorem familySup_le (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.familySup S hU ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    obtain ⟨x, hx, hb'⟩ := huU hb
    exact h x hx hb'
  exact z.closed u a huZ hEnt

end InfoSys
end DomainTheory.InformationSystems
