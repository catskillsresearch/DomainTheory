module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_consSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_subset_of_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_inter_ne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_empty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lmem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`L` is nested-or-disjoint** (Scott's "very special circumstance", generalizing
`ExampleB.cone_trichotomy`/`Example62`'s pairwise structure from `Bool` to `ℕ`-ary branching). -/
theorem L_nestedOrDisjoint : NestedOrDisjoint Lmem := by
  rintro X Y ⟨l, rfl⟩ ⟨l', rfl⟩
  induction l generalizing l' with
  | nil => exact Or.inr (Or.inl (by simp))
  | cons i s ih =>
    cases l' with
    | nil => exact Or.inl (by simp)
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rcases ih t with h1 | h2 | h3
        · exact Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h1)
        · exact Or.inr (Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h2))
        · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons, consSet_inter, h3, consSet_empty]))
      · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons]; exact consSet_inter_ne hij _ _))

end DomainTheory.NeighbourhoodSystems.Exercise724
