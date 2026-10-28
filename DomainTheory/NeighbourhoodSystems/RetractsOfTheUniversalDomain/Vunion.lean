module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem

def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)

def Vunion (n m : ℕ) : ℕ := canonIdx (VunionRaw n m)

theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals.cons, presentedIntervals.nil,
    Set.union_empty]
  rfl

namespace Uunion
open Domain.Recursive NeighborhoodSystem

theorem primrec : Nat.Primrec (fun t : ℕ => Uunion t.unpair.1 t.unpair.2) := by
  unfold Uunion
  exact (primrec_appendListCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Uunion
open Domain.Recursive NeighborhoodSystem

theorem V.master_nonempty : V.master.Nonempty := Set.univ_nonempty

theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

namespace Uunion
open Domain.Recursive NeighborhoodSystem

theorem eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals.append]
  rfl

end Uunion
section
open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

namespace splitFromBisection

theorem isSplitSpec' (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hQne : ∀ j, Q.X j ≠ ∅) :
    SplitSpec' W (splitFromBisection P hDiff B hWnomin) := by
  intro A B' hAB hBW Xn
  by_cases h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k
  · obtain ⟨n, m, k, rfl, rfl, rfl⟩ := h
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k]
    by_cases h1 : emptyInterDec P (Nat.pair n k) = 1
    · have hInterEmpty : P.X n ∩ P.X k = ∅ := (emptyInterDec.eq_one_iff P hpos hnomin n k).mp h1
      have hdiffEq : P.X n \ P.X k = P.X n := by
        ext x
        simp only [Set.mem_sdiff]
        exact ⟨fun hx => hx.1, fun hx =>
          ⟨hx, fun hxk => Set.eq_empty_iff_forall_notMem.mp hInterEmpty x ⟨hx, hxk⟩⟩⟩
      rw [ite_eq_left h1]
      refine ⟨Or.inl rfl, hBW, iff_of_true hInterEmpty rfl, ?_, Set.empty_union _,
        Set.empty_inter _⟩
      rw [hdiffEq]; exact hAB
    · by_cases h2 : IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) = 1
      · have hDiffEmpty : P.X n \ P.X k = ∅ :=
          (IsComputableDiff.emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mp h2
        have hInterEq : P.X n ∩ P.X k = P.X n := by
          ext x
          simp only [Set.mem_inter_iff]
          refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
          by_contra hxk
          exact Set.eq_empty_iff_forall_notMem.mp hDiffEmpty x ⟨hx, hxk⟩
        rw [ite_eq_right h1, ite_eq_left h2]
        refine ⟨hBW, Or.inl rfl, ?_, iff_of_true hDiffEmpty rfl, Set.union_empty _,
          Set.inter_empty _⟩
        rw [hInterEq]; exact hAB
      · have h1' : P.X n ∩ P.X k ≠ ∅ :=
          fun he => h1 ((emptyInterDec.eq_one_iff P hpos hnomin n k).mpr he)
        have h2' : P.X n \ P.X k ≠ ∅ :=
          fun he => h2 ((IsComputableDiff.emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mpr he)
        rw [ite_eq_right h1, ite_eq_right h2]
        exact ⟨Or.inr (Q.mem_X _), Or.inr (Q.mem_X _), iff_of_false h1' (hQne _),
          iff_of_false h2' (hQne _), B.union m, B.disjoint m⟩
  · unfold splitFromBisection
    rw [dite_eq_right h]
    exact splitChoice'_isSplitSpec W hWnomin hAB hBW Xn

end splitFromBisection
end ComputableBisection
end

open Domain.Recursive NeighborhoodSystem

theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection.isSplitSpec' VComputablePresentation V.isComputableDiff
    UBisection2 U.noMinimal V.isPositive V.noMinimal V.diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)

namespace Uunion
open Domain.Recursive NeighborhoodSystem

theorem spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion.eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion.eq_union]

end Uunion
open Domain.Recursive NeighborhoodSystem

theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection.isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V.noMinimal U.isPositive U.noMinimal U.diffClosed (fun j => (VX_nonempty j).ne_empty)

theorem U_union_exists (n m : ℕ) : ∃ k, UX k = UX n ∪ UX m := U_surj_UX (U_union_UX_mem n m)

theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩

def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion.primrec
  unionIdx_spec := Uunion.spec
  union_computable := U_union_computable

namespace levelSet
open Domain.Recursive NeighborhoodSystem

theorem myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet.union_same_level, myLor_eq_lor]

theorem VunionRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
namespace Vunion
open Domain.Recursive NeighborhoodSystem

theorem spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VunionRaw]

theorem spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion.spec n m

end Vunion
open Domain.Recursive NeighborhoodSystem

theorem V.union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion.spec n m⟩

theorem V.union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V.union_exists t.unpair.1 t.unpair.2) rfl⟩

namespace levelSet
open Domain.Recursive NeighborhoodSystem

theorem zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

end levelSet
open Domain.Recursive NeighborhoodSystem

theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx.eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet.zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx

set_option linter.unusedVariables false

theorem example_812_e_d : @DomainTheory.NeighbourhoodSystems.SplitSpec' Rat Nat DomainTheory.NeighbourhoodSystems.V
  DomainTheory.NeighbourhoodSystems.splitX812e :=
  @DomainTheory.NeighbourhoodSystems.hxSplit812e

theorem example_812_f : @DomainTheory.NeighbourhoodSystems.SplitSpec' Nat Rat DomainTheory.NeighbourhoodSystems.U
  DomainTheory.NeighbourhoodSystems.splitX812f :=
  @DomainTheory.NeighbourhoodSystems.hySplit812f

theorem example_812_g1a : @Eq (Set Rat) (DomainTheory.NeighbourhoodSystems.UX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Rat DomainTheory.NeighbourhoodSystems.U) :=
  DomainTheory.NeighbourhoodSystems.UX_zero

theorem example_812_g1b : @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Nat DomainTheory.NeighbourhoodSystems.V) :=
  DomainTheory.NeighbourhoodSystems.VX_zero

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion.spec'

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem VunionRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VunionRaw t.unpair.1 t.unpair.2) := by
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
  have hlor : Nat.Primrec (fun t : ℕ => myLor
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLor.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hlor).of_eq fun _ => rfl

theorem Vunion : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vunion t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VunionRaw).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

def V.isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec.Vunion
  unionIdx_spec := Vunion.spec'
  union_computable := V.union_computable

end DomainTheory.NeighbourhoodSystems
