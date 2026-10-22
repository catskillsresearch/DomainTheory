module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_Fun_compl_nbhd_iffu27
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagVal_and_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ` is recursively decidable, jointly in `(n,j,m)`.** Combines
`mem_Fun_compl_nbhd_iff'` (a bounded `∃c < n`) with `RecDecidable.bExists`, packed `(n,(j,m))`-style. -/
theorem mem_Fun_compl_nbhd_isComputable :
    RecDecidable (fun w : ℕ =>
      w.unpair.2.unpair.1 ∈ Fun (nbhd w.unpair.1)ᶜ (nbhd w.unpair.2.unpair.2)ᶜ) := by
  have hbitN : RecDecidable (fun w : ℕ => w.unpair.2.unpair.1.testBit w.unpair.1 = true) :=
    ⟨fun w => bitAt w.unpair.2.unpair.1 w.unpair.1,
      (primrec_bitAt.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq
        fun w => by simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hCJ' : RecDecidable (fun w : ℕ => untagVal w.unpair.1 = w.unpair.2.unpair.2.unpair.1 ∧
      ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2.unpair.2 i = 1) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (untagVal_and_isComputable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hp := hbitN.and hCJ'
  refine RecDecidable.of_iff (fun w => ?_) (hp.bExists Nat.Primrec.left)
  rw [mem_Fun_compl_nbhd_iff']
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems.Exercise723
