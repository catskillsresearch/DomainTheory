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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar_eq_zero_or_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LenumInter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

theorem LenumInter_spec {n m : ℕ} (h : ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :
    Lenum (LenumInter n m) = Lenum n ∩ Lenum m := by
  unfold LenumInter
  rcases isPrefixChar_eq_zero_or_one m n with h0 | h1
  · rw [h0, selectFn_zero]
    have hp : isPrefixChar n m = 1 := by
      rcases (Lenum_cons_iff n m).mp h with hp | hp
      · rw [h0] at hp; exact absurd hp (by decide)
      · exact hp
    exact (Set.inter_eq_right.mpr ((Lenum_subset_iff m n).mpr hp)).symm
  · rw [h1, selectFn_one]
    exact (Set.inter_eq_left.mpr ((Lenum_subset_iff n m).mpr h1)).symm

end DomainTheory.NeighbourhoodSystems.Exercise724
