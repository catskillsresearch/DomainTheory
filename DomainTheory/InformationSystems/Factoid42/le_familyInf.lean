/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid41
import DomainTheory.InformationSystems.Factoid42.Basic


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)



theorem le_familyInf (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element}
    (h : ∀ x ∈ S, z ≤ x) : z ≤ sys.familyInf S hne :=
  fun _a ha x hx => h x hx ha

end InfoSys
end DomainTheory.InformationSystems
