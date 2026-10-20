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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_false
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_true
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.embStr_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_two
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.master_ne_zero_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.master_ne_one_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.eq_master_of_master_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.subset_iff_eq_or_eq_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

/-- **Pointwise (sequential) conjunction on `T`**, as a two-variable approximable mapping:
`X, Y f Z ↔ mem X ∧ mem Y ∧ mem Z ∧ andFn X Y ⊆ Z` (Scott's "step" pattern again). -/
noncomputable def andMap2 : ApproximableMap₂ Example23.T Example23.T Example23.T where
  rel X Y Z := Example23.T.mem X ∧ Example23.T.mem Y ∧ Example23.T.mem Z ∧ andFn X Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨Example12.mem_master, Example12.mem_master, Example12.mem_master, by
    show andFn Example12.master Example12.master ⊆ Example12.master
    rw [andFn_master]⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, Example23.T.inter_mem hZ hZ' (andFn_mem hX hY) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
    · rw [andFn_master] at hsub
      have hZ'master : Z' = Example12.master := eq_master_of_master_subset (hsub.trans hZZ')
      rw [hZ'master, Example12.master]; exact Set.subset_univ _
    · rw [andFn_zero] at hsub
      have hX'eq : X' = zero :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_zero hX'X).resolve_right
          master_ne_zero_T.symm
      rw [hX'eq, andFn_zero]
      exact (hY'Y.trans hsub).trans hZZ'
    · rw [andFn_one] at hsub
      have hX'eq : X' = one :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_one hX'X).resolve_right
          master_ne_one_T.symm
      rw [hX'eq, andFn_one]
      exact hsub.trans hZZ'

end DomainTheory.NeighbourhoodSystems.Exercise724
