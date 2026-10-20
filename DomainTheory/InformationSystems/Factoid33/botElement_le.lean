/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid32
import DomainTheory.InformationSystems.Factoid33.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `⊥` is least. -/
theorem botElement_le (x : sys.Element) : sys.botElement ≤ x := by
  intro a ha
  have hsub : (↑({sys.bot} : Finset α) : Set α) ⊆ x.carrier := by
    intro b hb
    have hb' : b ∈ ({sys.bot} : Finset α) := Finset.mem_coe.1 hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    exact factoid_3_2 sys x
  exact x.closed {sys.bot} a hsub ha

end InfoSys
end DomainTheory.InformationSystems
