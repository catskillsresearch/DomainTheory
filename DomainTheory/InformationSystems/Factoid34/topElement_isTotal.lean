/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.Factoid34.Basic
public import DomainTheory.InformationSystems.Factoid34.le_topElement

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




theorem topElement_isTotal (h : sys.AllConsistent) :
    sys.IsTotal (sys.topElement h) := fun y _ => sys.le_topElement h y

end InfoSys
end DomainTheory.InformationSystems
