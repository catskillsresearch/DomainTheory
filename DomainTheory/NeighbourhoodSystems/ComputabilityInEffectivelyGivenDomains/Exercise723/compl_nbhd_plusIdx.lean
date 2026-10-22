module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_sumSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusIdx_testBit

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`plusIdx`'s excluded set is the Minkowski sum `Eₙ + Eₘ`.** -/
theorem compl_nbhd_plusIdx (n m : ℕ) : (nbhd (plusIdx n m))ᶜ = (nbhd n)ᶜ +ˢ (nbhd m)ᶜ := by
  rw [compl_nbhd, compl_nbhd, compl_nbhd]
  ext k
  simp only [mem_sumSet, Set.mem_ofPred_eq, plusIdx_testBit]
  constructor
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, ha, k - a, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, by omega, ha, by rw [Nat.add_sub_cancel_left]; exact hb⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
