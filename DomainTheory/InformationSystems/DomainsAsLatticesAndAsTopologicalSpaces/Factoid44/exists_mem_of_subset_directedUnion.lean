/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Given `Y` whose tokens each lie in some member of a nonempty directed family, find a
single member containing all of `Y`. -/
theorem exists_mem_of_subset_directedUnion (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) (Y : Finset α)
    (hY : (Y : Set α) ⊆ sys.familyUnionCarrier S) :
    ∃ z ∈ S, (Y : Set α) ⊆ z.carrier := by
  induction Y using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))⟩
  | insert a s _ha ih =>
    have ha' : ∃ x ∈ S, a ∈ x.carrier :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ sys.familyUnionCarrier S := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨xa, hxa, haS⟩ := ha'
    obtain ⟨xs, hxs, hsS⟩ := ih hs'
    obtain ⟨z, hz, hxa_le, hxs_le⟩ := hdir xa xs hxa hxs
    refine ⟨z, hz, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hb) with rfl | hb'
    · exact hxa_le haS
    · exact hxs_le (hsS (Finset.mem_coe.2 hb'))

end InfoSys

end DomainTheory.InformationSystems
