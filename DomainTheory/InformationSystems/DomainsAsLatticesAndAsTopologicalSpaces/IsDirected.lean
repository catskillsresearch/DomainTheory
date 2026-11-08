module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Chain

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def IsDirected (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → ∃ z ∈ S, x ≤ z ∧ y ≤ z

namespace IsDirected

theorem of_IsChain {S : Set sys.Element} (h : sys.Chain S) : sys.IsDirected S := by
  intro x y hx hy
  rcases h.out x y hx hy with hxy | hyx
  · exact ⟨y, hy, hxy, le_rfl⟩
  · exact ⟨x, hx, le_rfl, hyx⟩

theorem exists_mem_of_subset_union (S : Set sys.Element) (hne : S.Nonempty)
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

theorem finitelyConsistent (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  obtain ⟨z, _hz, hYZ⟩ := exists_mem_of_subset_union sys S hne hdir Y hY
  exact z.consistent Y hYZ

end IsDirected

end InfoSys
end DomainTheory.InformationSystems
