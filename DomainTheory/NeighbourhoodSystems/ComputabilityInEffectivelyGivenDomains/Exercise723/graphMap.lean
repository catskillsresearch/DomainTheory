module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_subset_compl_of_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_inter_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.GraphIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.GraphIdx_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **`graph` as an approximable map** `(PN → PN) → PN`, dually to `gMap`'s "reversal idiom":
`Zᶜ ⊆ GraphIdx W`. -/
def graphMap : ApproximableMap (funSpace PN PN) PN where
  rel W Z := (funSpace PN PN).mem W ∧ PN.mem Z ∧ Zᶜ ⊆ GraphIdx W
  rel_dom := fun ⟨h, _, _⟩ => h
  rel_cod := fun ⟨_, h, _⟩ => h
  master_rel := ⟨(funSpace PN PN).master_mem, PN.master_mem, by
    show (Set.univ : Set ℕ)ᶜ ⊆ GraphIdx Set.univ
    intro x hx
    exact absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨hW, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨k', rfl⟩ := hZ'
    refine ⟨hW', ⟨k', rfl⟩, ?_⟩
    calc (nbhd k')ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ GraphIdx W := hsub
      _ ⊆ GraphIdx W' := GraphIdx_mono hW'W

end DomainTheory.NeighbourhoodSystems.Exercise723
