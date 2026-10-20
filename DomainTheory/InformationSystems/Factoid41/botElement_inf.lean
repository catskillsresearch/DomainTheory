/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid41.Basic
import DomainTheory.InformationSystems.Factoid41.le_iff_inf_eq


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `⊥` is a zero for meet: `⊥ ∩ x = ⊥`. -/
theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (sys.le_iff_inf_eq (x := sys.botElement) (y := x)).1 (sys.botElement_le x)

end InfoSys
end DomainTheory.InformationSystems
