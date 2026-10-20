/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf_le_left

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 4.1.** `x ⊆ y` iff `x ∩ y = x`. -/
theorem le_iff_inf_eq {x y : sys.Element} : x ≤ y ↔ sys.inf x y = x := by
  constructor
  · intro h
    refine le_antisymm (sys.inf_le_left x y) ?_
    intro a ha
    exact ⟨ha, h ha⟩
  · intro heq
    have hc : x.carrier = x.carrier ∩ y.carrier :=
      Eq.symm (congrArg Element.carrier heq)
    intro a ha
    exact ((Set.ext_iff.1 hc a).1 ha).2

end InfoSys
end DomainTheory.InformationSystems
