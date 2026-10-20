/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid41.Basic


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem le_inf {x y z : sys.Element} (hxy : x ≤ y) (hxz : x ≤ z) : x ≤ sys.inf y z :=
  fun _ ha => ⟨hxy ha, hxz ha⟩

end InfoSys
end DomainTheory.InformationSystems
