module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.gMap_rel_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.testBit_imp_mem_Fun_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_nbhd_subset_Fun_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **`gMap` is computable.** The neighbourhood relation `gMap_rel_iff` reduces (via
`compl_nbhd_subset_Fun_iff`) to a bounded `∀j < k`, primitive recursive by
`testBit_imp_mem_Fun_isComputable`/`RecDecidable.bForall`. -/
theorem gMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres gMap := by
  have hall : RecDecidable (fun u : ℕ => ∀ j, j < u.unpair.2 →
      u.unpair.2.testBit j = true →
        j ∈ Fun (nbhd u.unpair.1.unpair.1)ᶜ (nbhd u.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun u => by simp only [unpair_pair_fst, unpair_pair_snd])
      (testBit_imp_mem_Fun_isComputable.bForall Nat.Primrec.right)
  refine (RecDecidable.of_iff (fun t => ?_) hall).re
  simp only [prodPresentation_X]
  exact (gMap_rel_iff _ _ _).trans (compl_nbhd_subset_Fun_iff _ _ _)

end DomainTheory.NeighbourhoodSystems.Exercise723
