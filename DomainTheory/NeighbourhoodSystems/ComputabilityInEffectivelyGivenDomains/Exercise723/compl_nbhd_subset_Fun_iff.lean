module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_compl_nbhd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`(nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ`, bounded-quantifier form.** Every excluded point of
`nbhd k` is below `k` (`lt_of_testBit_true`), so the subset test is a bounded `∀j < k`. -/
theorem compl_nbhd_subset_Fun_iff (n m k : ℕ) : (nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
    ∀ j, j < k → (k.testBit j = true → j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ) := by
  constructor
  · intro h j _ hj
    exact h (mem_compl_nbhd.mpr hj)
  · intro h j hj
    rw [mem_compl_nbhd] at hj
    exact h j (lt_of_testBit_true hj) hj

end DomainTheory.NeighbourhoodSystems.Exercise723
