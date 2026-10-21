/-ai
Two enumerated neighbourhoods have a common enumerated lower bound if and only if one address is a prefix of the other. If they are nested, the more specific is itself a witness. A common lower bound forces nestedness, because a disjoint pair has no nonempty common lower bound and every enumerated neighbourhood is nonempty.

From a common lower bound, the nested-or-disjoint property gives one inclusion, the other inclusion, or an empty intersection. An inclusion is a prefix characteristic equal to one. An empty intersection cannot contain a point of the nonempty neighbourhood of the witness. Conversely, if one prefix characteristic is one, the corresponding enumerated neighbourhood is contained in the intersection by the subset criterion.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_consSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_empty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **7.1(ii) — consistency is recursively decidable.** `∃ k, Lenum k ⊆ Lenum n ∩ Lenum m` holds
iff `n, m` are nested (`isPrefixChar m n = 1 ∨ isPrefixChar n m = 1`): if nested, the more specific
of `n, m` itself witnesses it; conversely a common lower bound forces nestedness by
`L_nestedOrDisjoint` (a properly disjoint pair has no nonempty common lower bound, and every
`Lmem` set is nonempty). -/
theorem Lenum_cons_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
    · exact Or.inl ((isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h))
    · exact Or.inr ((isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h))
    · exfalso
      unfold Lenum at hk
      obtain ⟨t, ht⟩ := nbhd_nonempty (decodeList k)
      exact Set.notMem_empty t (h ▸ hk ht)
  · rintro (hp | hp)
    · exact ⟨n, Set.subset_inter subset_rfl ((Lenum_subset_iff n m).mpr hp)⟩
    · exact ⟨m, Set.subset_inter ((Lenum_subset_iff m n).mpr hp) subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
