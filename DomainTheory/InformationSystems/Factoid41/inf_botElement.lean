/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid41.Basic
import DomainTheory.InformationSystems.Factoid41.inf_comm
import DomainTheory.InformationSystems.Factoid41.botElement_inf


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_botElement (x : sys.Element) : sys.inf x sys.botElement = sys.botElement := by
  rw [sys.inf_comm, sys.botElement_inf]

end InfoSys
end DomainTheory.InformationSystems
