/-ai
The flattening combinator from the double power domain into the power domain relates a neighbourhood A to a neighbourhood B when every neighbourhood X belonging to a member of A is contained in some member of B. The master neighbourhoods are related because every neighbourhood lies under the master. An intersection of targets is related because the two covering neighbourhoods meet in a neighbourhood, which lands back in both targets by downward closure. A smaller source and a larger target remain related because the condition only quantifies over membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*}

/-- **Exercise 7.20 (Scott 1981, PRG-19) — the flattening combinator `union : ℙ(ℙD) → ℙD`.** Given a
`ℙℙD`-neighbourhood `A` and a `ℙD`-neighbourhood `B`, the relation holds iff every `D`-neighbourhood
`X` occurring in some member-set `S ∈ A` is covered by some `Y ∈ B`. This is the
representation-independent form of Scott's displayed `∀ i<n ∀ j<m_i ∃ k<q. X_{ij} ⊆ Y_k`
(see `unionMap_rel_fin`). It is the multiplication `μ` of the power-domain monad. -/
def unionMap (V : NeighborhoodSystem α) :
    ApproximableMap V.PowerDomain.PowerDomain V.PowerDomain where
  rel A B := V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨V.PowerDomain.PDmem_master, V.PDmem_master, ?_⟩
    intro S hS X hX
    simp only [mem_upSet] at hS
    exact ⟨V.master, ⟨V.master_mem, subset_rfl⟩, V.sub_master (V.PDmem_mem hS.1 hX)⟩
  inter_right := by
    rintro A B B' ⟨hA, hB, hbody⟩ ⟨-, hB', hbody'⟩
    refine ⟨hA, V.PDmem_inter hB hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S hS X hX
    obtain ⟨Y', hY'B', hXY'⟩ := hbody' S hS X hX
    have hXmem : V.mem X := V.PDmem_mem (V.PowerDomain.PDmem_mem hA hS) hX
    have hYmem : V.mem Y := V.PDmem_mem hB hYB
    have hY'mem : V.mem Y' := V.PDmem_mem hB' hY'B'
    have hsub : X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hinmem : V.mem (Y ∩ Y') := V.inter_mem hYmem hY'mem hXmem hsub
    exact ⟨Y ∩ Y', Set.mem_inter
      (V.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (V.PDmem_down hB' hY'B' Set.inter_subset_right hinmem), hsub⟩
  mono := by
    rintro A A' B B' ⟨_, _, hbody⟩ hA'A hBB' hA' hB'
    refine ⟨hA', hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S (hA'A hS) X hX
    exact ⟨Y, hBB' hYB, hXY⟩

end DomainTheory.NeighbourhoodSystems
