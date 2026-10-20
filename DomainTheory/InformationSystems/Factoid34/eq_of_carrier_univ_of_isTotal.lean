/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.InfoSys
import DomainTheory.InformationSystems.Factoid34.Basic


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




/-- Conversely: any total element equals an element with carrier `D`. -/
theorem eq_of_carrier_univ_of_isTotal {x t : sys.Element}
    (hx : x.carrier = Set.univ) (ht : sys.IsTotal t) : t = x :=
  le_antisymm (fun _ _ => hx ▸ trivial) (ht x (fun _ _ => hx ▸ trivial))

end InfoSys
end DomainTheory.InformationSystems
