/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Proposition23
import DomainTheory.InformationSystems.Factoid35.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `u ⊆ ū`. -/
theorem subset_closure {u : Finset α} (hu : u ∈ sys.Con) :
    ↑u ⊆ (sys.closure u hu).carrier :=
  fun _ hX => sys.ent_refl hu (Finset.mem_coe.1 hX)

end InfoSys
end DomainTheory.InformationSystems
