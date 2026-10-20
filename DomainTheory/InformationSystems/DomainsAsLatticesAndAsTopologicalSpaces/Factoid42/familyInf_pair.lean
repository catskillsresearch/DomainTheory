/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf_le
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.le_familyInf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)



/-- Binary meet agrees with the two-element family meet. -/
theorem familyInf_pair (x y : sys.Element) :
    sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf
      (sys.familyInf_le _ _ (Set.mem_insert x {y}))
      (sys.familyInf_le _ _ (Set.mem_insert_of_mem _ rfl))
  · apply sys.le_familyInf
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact sys.inf_le_left _ _
    · have : z = y := hy
      subst this
      exact sys.inf_le_right _ _

end InfoSys
end DomainTheory.InformationSystems
