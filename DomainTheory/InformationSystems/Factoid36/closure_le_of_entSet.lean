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

/-- If `w` entails every member of `u`, then `ū ⊆ w̄`. -/
theorem closure_le_of_entSet {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (h : sys.EntSet w u) : sys.closure u hu ≤ sys.closure w hw := by
  intro a ha
  exact sys.ent_trans hw hu h ha

end InfoSys
end DomainTheory.InformationSystems
