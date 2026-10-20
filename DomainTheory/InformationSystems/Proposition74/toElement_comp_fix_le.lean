/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Fixpoint
import DomainTheory.InformationSystems.Proposition54
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Proposition74.Basic
import DomainTheory.InformationSystems.Proposition74.proposition_7_4_ii


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem toElement_comp_fix_le (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    g.toElement (h.toElement (fixElement A f)) ≤ h.toElement (fixElement A f) := by
  have h1 : g.toElement (h.toElement (fixElement A f)) =
      h.toElement (f.toElement (fixElement A f)) := by
    rw [← comp_toElement, ← hcomm, comp_toElement]
  rw [h1, proposition_7_4_ii A f]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
