module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The difference index: `canonIdx` of the raw difference code `VdiffRaw`. -/
def Vdiff (n m : ℕ) : ℕ := canonIdx (VdiffRaw n m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- **The "same level" set-difference formula**, mirroring `Exercise812.lean`'s
`levelSet.inter_same_level` exactly (`&&&` becomes the "and-not" combinator `a ^^^ (a &&& b)`,
via `testBit.xor_and_self`). -/
theorem diff_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ \ levelSet k m₂ = levelSet k (m₁ ^^^ (m₁ &&& m₂)) := by
  ext n; simp [levelSet]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet.diff_same_level`, upsampled to a common level** — mirrors
`levelSet.myInter` exactly, substituting `myAndNot` for `myLand`. -/
theorem myDiff (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 \ levelSet k2 m2
      = levelSet (max k1 k2) (myAndNot (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) (m := m1),
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) (m := m2)]
  rw [levelSet.diff_same_level, myAndNot_eq]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- **`VdiffRaw` realizes `VX n \ VX m`** at the `levelSet` level (unconditionally). -/
theorem VdiffRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.2 = VX n \ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myDiff (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Vdiff

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, mirroring
`Vcons_iff_nonempty_inter`. -/
theorem iff_nonempty (n m : ℕ) :
    (∃ k, VX k = VX n \ VX m) ↔ (VX n \ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact VX_nonempty k
  · intro hne
    rw [← levelSet.VdiffRaw] at hne
    have hVmem : V.mem (VX n \ VX m) := by
      rw [← levelSet.VdiffRaw]
      exact ⟨(VdiffRaw n m).unpair.1, (VdiffRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, hk⟩

end Vdiff
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Vdiff

open Domain.Recursive NeighborhoodSystem

theorem spec {n m : ℕ} (h : ∃ k, VX k = VX n \ VX m) : VX (Vdiff n m) = VX n \ VX m := by
  have hne : (levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VdiffRaw]; obtain ⟨k, hk⟩ := h; rw [← hk]; exact VX_nonempty k
  unfold Vdiff
  rw [VX_canonIdx]
  show levelSet (canonIdx (VdiffRaw n m)).unpair.1 (canonIdx (VdiffRaw n m)).unpair.2 = VX n \ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VdiffRaw]

end Vdiff
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem lowXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.lowXor t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp
    (primrec_add₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right))).of_eq
    fun _ => rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem xorStep : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => _root_.DomainTheory.NeighbourhoodSystems.lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec.lowXor.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem myXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myXor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.xorStep w.unpair.2.unpair.2) :=
    primrec.xorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem myAndNot : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myLand t.unpair.1 t.unpair.2) := primrec.myLand
  exact (primrec.myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.myAndNot, unpair_pair_fst, unpair_pair_snd]

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem VdiffRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1) := primrec.canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2) := primrec.canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) :=
    (primrec.myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) :=
    (primrec.myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have handnot : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myAndNot
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec.myAndNot.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair handnot).of_eq fun _ => rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`\`, for `V`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable. -/
theorem V_diff_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n \ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VdiffRaw t.unpair.1 t.unpair.2) := primrec.VdiffRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec.myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty.le_one (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vdiff.iff_nonempty, ← levelSet.VdiffRaw,
      myLevelSetNonempty.eq_one_iff]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem Vdiff : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vdiff t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VdiffRaw).of_eq fun _ => rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec.Vdiff
  diffIdx_spec := Vdiff.spec
  diff_computable := V_diff_computable

end DomainTheory.NeighbourhoodSystems
