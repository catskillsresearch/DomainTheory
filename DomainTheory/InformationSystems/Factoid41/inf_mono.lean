/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid41.Basic
import DomainTheory.InformationSystems.Factoid41.inf_le_left
import DomainTheory.InformationSystems.Factoid41.inf_le_right
import DomainTheory.InformationSystems.Factoid41.le_inf


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_mono {x₁ x₂ y₁ y₂ : sys.Element} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    sys.inf x₁ y₁ ≤ sys.inf x₂ y₂ :=
  sys.le_inf (le_trans (sys.inf_le_left _ _) hx) (le_trans (sys.inf_le_right _ _) hy)

end InfoSys
end DomainTheory.InformationSystems
