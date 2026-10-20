/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Fixpoint.Basic
public import DomainTheory.InformationSystems.Fixpoint.fixElement_le_of_pre_fixed
public import DomainTheory.InformationSystems.Fixpoint.toElement_fixElement_le

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)














namespace ApproximableMap




/-- **Theorem 7.3.** `fix(f)` is a fixed point. -/
theorem fixElement_fixed (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f := by
  apply le_antisymm
  · exact toElement_fixElement_le A f
  · have hpre : f.toElement (f.toElement (fixElement A f)) ≤
        f.toElement (fixElement A f) :=
      toElement_mono f (toElement_fixElement_le A f)
    exact fixElement_le_of_pre_fixed A f (f.toElement (fixElement A f)) hpre

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
