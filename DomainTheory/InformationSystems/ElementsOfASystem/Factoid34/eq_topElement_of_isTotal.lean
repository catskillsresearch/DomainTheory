/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.le_topElement

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




/-- When `⊤` exists, it is the unique total element. -/
theorem eq_topElement_of_isTotal (h : sys.AllConsistent) {x : sys.Element}
    (hx : sys.IsTotal x) : x = sys.topElement h :=
  le_antisymm (sys.le_topElement h x) (hx _ (sys.le_topElement h x))

end InfoSys
end DomainTheory.InformationSystems
