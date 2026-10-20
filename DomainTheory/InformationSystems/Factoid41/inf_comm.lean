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


theorem inf_comm (x y : sys.Element) : sys.inf x y = sys.inf y x := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf (sys.inf_le_right x y) (sys.inf_le_left x y)
  · exact sys.le_inf (sys.inf_le_right y x) (sys.inf_le_left y x)

end InfoSys
end DomainTheory.InformationSystems
