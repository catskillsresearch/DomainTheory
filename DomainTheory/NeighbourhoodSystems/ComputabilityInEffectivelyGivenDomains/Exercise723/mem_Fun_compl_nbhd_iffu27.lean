module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_compl_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_bitsCodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_Fun_compl_nbhd_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **Bounded-quantifier reformulation** of `mem_Fun_compl_nbhd_iff`, avoiding `decodeList`/
`bitsCode` for the outer existential (feeding directly into `RecDecidable.bExists`). -/
theorem mem_Fun_compl_nbhd_iff' (n m j : ℕ) :
    j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
      ∃ c, c < n ∧ n.testBit c = true ∧ untagVal c = j ∧
        ∀ i ∈ decodeList (untagList c), bitAt m i = 1 := by
  rw [mem_Fun_compl_nbhd_iff]
  simp only [mem_bitsCodeList, mem_compl_nbhd, bitAt_eq_one_iff]
  constructor
  · rintro ⟨c, hbit, hval, hall⟩
    exact ⟨c, lt_of_testBit_true hbit, hbit, hval, hall⟩
  · rintro ⟨c, -, hbit, hval, hall⟩
    exact ⟨c, hbit, hval, hall⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
