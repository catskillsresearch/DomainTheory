/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid41.Basic
public import DomainTheory.InformationSystems.Factoid41.inf_le_left
public import DomainTheory.InformationSystems.Factoid41.inf_le_right
public import DomainTheory.InformationSystems.Factoid41.le_inf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_assoc (x y z : sys.Element) : sys.inf (sys.inf x y) z = sys.inf x (sys.inf y z) := by
  refine le_antisymm ?_ ?_
  · refine sys.le_inf ?_ (sys.le_inf ?_ ?_)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_right _ _)
    · exact sys.inf_le_right _ _
  · refine sys.le_inf (sys.le_inf ?_ ?_) ?_
    · exact sys.inf_le_left _ _
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_right _ _)

end InfoSys
end DomainTheory.InformationSystems
