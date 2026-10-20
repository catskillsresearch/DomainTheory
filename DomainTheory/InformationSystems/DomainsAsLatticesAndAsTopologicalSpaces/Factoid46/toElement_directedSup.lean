/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- Approximable maps preserve directed lubs (Scott continuity on elements). -/
theorem toElement_directedSup (f : ApproximableMap A B)
    (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S) :
    f.toElement (A.directedSup S hne hdir) =
      B.directedSup (f.toElement '' S) (nonempty_image hne f.toElement)
        (directed_image hdir f.toElement f.toElement_mono) := by
  refine le_antisymm ?_ ?_
  · intro Y ⟨u, hu, hrel⟩
    have huU : (u : Set α) ⊆ A.familyUnionCarrier S := by
      intro a ha
      have : a ∈ (A.directedSup S hne hdir).carrier := hu ha
      rwa [A.directedSup_carrier_eq_union S hne hdir] at this
    obtain ⟨z, hz, huZ⟩ := A.exists_mem_of_subset_directedUnion S hne hdir u huU
    have : Y ∈ (f.toElement z).carrier := ⟨u, huZ, hrel⟩
    rw [B.directedSup_carrier_eq_union]
    exact ⟨f.toElement z, ⟨z, hz, rfl⟩, this⟩
  · apply B.directedSup_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact f.toElement_mono (A.le_directedSup S hne hdir hx)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
