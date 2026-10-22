
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_injective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`Xₙ ∩ Xₘ = X_k` on the `Lenum` coding.** The intersection of two `nbhd`s is the more specific
of the two whenever they are nested, and no `Lmem` set at all otherwise (`nbhd` is always
nonempty, so `∅` never equals an `Lenum k`). -/
theorem Lenum_interEq_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  unfold Lenum
  rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
  · have hp : isPrefixChar m n = 1 := (isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_left.mpr h]
    constructor
    · intro heq; exact Or.inl ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨-, heq⟩ | ⟨hp', heq⟩)
      · rw [heq]
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList m) (decodeList n)).mpr hp')
  · have hp : isPrefixChar n m = 1 := (isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_right.mpr h]
    constructor
    · intro heq; exact Or.inr ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨hp', heq⟩ | ⟨-, heq⟩)
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList n) (decodeList m)).mpr hp')
      · rw [heq]
  · rw [h]
    have h1 : isPrefixChar m n ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList n))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ht ((nbhd_subset_iff _ _).mpr hp ht))
    have h2 : isPrefixChar n m ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList m))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ((nbhd_subset_iff _ _).mpr hp ht) ht)
    constructor
    · intro heq; exact absurd heq.symm (nbhd_nonempty (decodeList k)).ne_empty
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
      · exact absurd hp h1
      · exact absurd hp h2

end DomainTheory.NeighbourhoodSystems.Exercise724
