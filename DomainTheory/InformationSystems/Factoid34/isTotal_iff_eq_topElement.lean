/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.InfoSys
import DomainTheory.InformationSystems.Factoid34.Basic
import DomainTheory.InformationSystems.Factoid34.topElement_isTotal
import DomainTheory.InformationSystems.Factoid34.eq_topElement_of_isTotal


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




theorem isTotal_iff_eq_topElement (h : sys.AllConsistent) {x : sys.Element} :
    sys.IsTotal x ↔ x = sys.topElement h :=
  ⟨sys.eq_topElement_of_isTotal h, fun hx => hx ▸ sys.topElement_isTotal h⟩

end InfoSys
end DomainTheory.InformationSystems
