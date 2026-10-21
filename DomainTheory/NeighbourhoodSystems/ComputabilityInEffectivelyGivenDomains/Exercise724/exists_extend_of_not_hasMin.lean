/-ai
If an element x of L has no least neighbourhood and the neighbourhood of a list l belongs to x, then the neighbourhood of some one-element extension of l also belongs to x.

If every neighbourhood belonging to x contained the neighbourhood of l, that neighbourhood would be least. Thus some neighbourhood Y belonging to x fails to contain it. Write Y as the neighbourhood of a list l'. The two neighbourhoods are nested or disjoint. Containment of the neighbourhood of l in the neighbourhood of l' contradicts the choice of Y. If the neighbourhood of l' is contained in the neighbourhood of l, then l is a prefix of l'. The lists differ, since a common list would give a reflexive containment, so l is strictly shorter, and some one-element extension of l is still a prefix of l'. Upward closure returns the neighbourhood of that extension to x. If the neighbourhoods are disjoint, their intersection belongs to x and is empty, so the neighbourhood recovered from that membership equals the empty set, contradicting that every list neighbourhood is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_cons_prefix_of_prefix_of_length_lt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **One-step extension exists whenever `x` has no minimum.** If `x.mem (nbhd l)` and `x` has no
smallest neighbourhood, some length-`(l.length + 1)` extension `l ++ [i]` is also in `x`: pick any
`Y ∈ x.mem` witnessing that `nbhd l` is not the minimum (`hx`), which — being nested with `nbhd l`
(disjointness is impossible, `x.inter_mem` would force `L.mem ∅`) and *not* containing it — is a
strictly smaller neighbourhood `nbhd l' ⊊ nbhd l`; the first new list entry of `l'` past `l` is the
witness `i`. -/
theorem exists_extend_of_not_hasMin {x : L.Element} (hx : ¬ HasMin x) {l : List ℕ}
    (hl : x.mem (nbhd l)) : ∃ i, x.mem (nbhd (l ++ [i])) := by
  have hex : ∃ Y, x.mem Y ∧ ¬ nbhd l ⊆ Y := by
    by_contra hc; push Not at hc; exact hx ⟨nbhd l, hl, hc⟩
  obtain ⟨Y, hYmem, hnsub⟩ := hex
  obtain ⟨l', rfl⟩ := x.sub hYmem
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd l') with hsub | hsub | hdisj
  · exact absurd hsub hnsub
  · have hpre : l <+: l' := (nbhd_subset_iff l' l).mp hsub
    have hne : l ≠ l' := by rintro rfl; exact hnsub subset_rfl
    have hlt : l.length < l'.length :=
      lt_of_le_of_ne hpre.length_le (fun heqlen => hne (hpre.eq_of_length heqlen))
    obtain ⟨i, hi⟩ := exists_cons_prefix_of_prefix_of_length_lt hpre hlt
    exact ⟨i, x.up_mem hYmem (mem_nbhd _) ((nbhd_subset_iff l' (l ++ [i])).mpr hi)⟩
  · exfalso
    have hxmem : x.mem (nbhd l ∩ nbhd l') := x.inter_mem hl hYmem
    rw [hdisj] at hxmem
    obtain ⟨l'', hl''⟩ := x.sub hxmem
    exact (nbhd_nonempty l'').ne_empty hl''.symm

end DomainTheory.NeighbourhoodSystems.Exercise724
