/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid36.Basic
import DomainTheory.InformationSystems.Factoid36.closure_le_of_entSet


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Monotonicity of closure under inclusion of consistent sets. -/
theorem closure_le_of_subset {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (hsub : u ⊆ w) : sys.closure u hu ≤ sys.closure w hw :=
  sys.closure_le_of_entSet hu hw fun _ hy => sys.ent_refl hw (hsub hy)

end InfoSys
end DomainTheory.InformationSystems
