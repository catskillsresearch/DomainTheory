/-ai
The approximable map gMap from the product of PN with itself to PN interprets the operation Fun on positive information. A product neighbourhood of X and Y is related to Z when X, Y, and Z are neighbourhoods and the complement of Z is contained in Fun of the complements of X and Y. Domain and codomain membership are the product and the output neighbourhood. The master case uses that the complement of the whole set is empty. The intersection of two related outputs rewrites by the complement of a neighbourhood intersection and takes the union of the two Fun inclusions. Monotonicity shrinks the output by antitonicity of complement, keeps the original Fun inclusion, and enlarges the Fun set by monotonicity of Fun applied to the complemented input inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_subset_compl_of_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_inter_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **`λx,y. Fun x y` as an approximable map** `PN × PN → PN`, built by the same "reversal" idiom as
`plusMap`: `Zᶜ ⊆ Fun Xᶜ Yᶜ`. `funMap` (the actual `fun` combinator of Exercise 5.14, a map
`PN → (PN →⃗ PN)`) is `curry gMap` (`Theorem75.curry`). -/
def gMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ Zᶜ ⊆ Fun Xᶜ Yᶜ
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    fun x hx => absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ ⟨X', Y', heq, _, _, hZ', hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    refine ⟨X', Y', rfl, hX', hY', hZ', ?_⟩
    calc Z'ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ Fun Xᶜ Yᶜ := hsub
      _ ⊆ Fun X'ᶜ Y'ᶜ :=
        Fun_mono (compl_subset_compl_of_subset hXX') (compl_subset_compl_of_subset hYY')

end DomainTheory.NeighbourhoodSystems.Exercise723
