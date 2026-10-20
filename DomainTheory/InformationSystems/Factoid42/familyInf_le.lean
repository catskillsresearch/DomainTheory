/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Factoid41
public import DomainTheory.InformationSystems.Factoid42.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)



theorem familyInf_le (S : Set sys.Element) (hne : S.Nonempty) {x : sys.Element}
    (hx : x ∈ S) : sys.familyInf S hne ≤ x :=
  fun _a ha => ha x hx

end InfoSys
end DomainTheory.InformationSystems
