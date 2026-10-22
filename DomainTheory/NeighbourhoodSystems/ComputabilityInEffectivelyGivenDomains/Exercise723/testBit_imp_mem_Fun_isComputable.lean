
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_Fun_compl_nbhd_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **The implication guarding a single bit of `nbhd k`'s excluded set is recursively decidable,
jointly in `(j,n,m,k)`.** Packed `(j,((n,m),k))`-style. -/
theorem testBit_imp_mem_Fun_isComputable :
    RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true →
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) := by
  have hktest : RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true) :=
    ⟨fun w => bitAt w.unpair.2.unpair.2 w.unpair.1,
      (primrec_bitAt.comp ((Nat.Primrec.right.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq
        fun w => by simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hmem2 : RecDecidable (fun w : ℕ =>
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (mem_Fun_compl_nbhd_isComputable.comp
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.pair (Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)))))
  refine RecDecidable.of_iff (fun w => ?_) (hktest.not.or hmem2)
  constructor
  · intro h
    rcases hktest.em w with hb | hb
    · exact Or.inr (h hb)
    · exact Or.inl hb
  · rintro (hb | hb) hbit
    · exact absurd hbit hb
    · exact hb

end DomainTheory.NeighbourhoodSystems.Exercise723
