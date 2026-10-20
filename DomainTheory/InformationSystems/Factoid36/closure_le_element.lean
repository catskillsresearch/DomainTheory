/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid36.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Finite approximations below `x` really do approximate `x`. -/
theorem closure_le_element (x : sys.Element) {u : Finset α} (hu : u ∈ sys.Con)
    (hsub : ↑u ⊆ x.carrier) : sys.closure u hu ≤ x := by
  intro a ha
  exact x.closed u a hsub ha

end InfoSys
end DomainTheory.InformationSystems
