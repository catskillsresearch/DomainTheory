module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.part_e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f.isComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_5
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.part_e_domain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The union index: list-concatenate the two canonicalized presenting lists. `UX` re-canonicalizes
on lookup, so no further canonicalization of the inputs is needed here (mirrors `Udiff`). -/
def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The union index: `canonIdx` of the raw union code `VunionRaw`. -/
def Vunion (n m : ℕ) : ℕ := canonIdx (VunionRaw n m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hX0`: index `0` presents `U`'s master neighbourhood. `decodeQPairList 0 = []`
(`decodeList_zero`), so `canonList` falls back to its `[(0,1)]` branch, which presents
`U.master` exactly as in `U_mem_presentedIntervals_canonList`. -/
theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]
  rfl

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Uunion

open Domain.Recursive NeighborhoodSystem

theorem primrec : Nat.Primrec (fun t : ℕ => Uunion t.unpair.1 t.unpair.2) := by
  unfold Uunion
  exact (primrec_appendListCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Uunion
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hD₁mne` for `V`: the master neighbourhood `V.master = Set.univ` is non-empty. -/
theorem V_master_nonempty : V.master.Nonempty := Set.univ_nonempty

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Uunion

open Domain.Recursive NeighborhoodSystem

/-- **`Uunion` realizes set union at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — concatenating presenting lists always presents the union, no consistency case
split needed (the one respect in which `∪` is even simpler than `\`'s `Udiff.eq_diff`). -/
theorem eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals_append]
  rfl

end Uunion
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)


namespace splitFromBisection
/-- **`splitFromBisection` satisfies `SplitSpec'`**, completing the concrete-construction half of
`8.12(g)(3)`. Needs one extra hypothesis beyond `isComputableSplit.ofBisection`'s own,
`hQne : ∀ j, Q.X j ≠ ∅` — true for both `U`/`V` (every `ComputablePresentation` index is `mem`-
genuine, and both systems' `mem` structurally excludes `∅`; see `Exercise812.lean` line 199/
`Definition87.lean` line 96) but not derivable from `ComputableBisection`'s abstract fields alone
(nothing there stops `Q.X (B.left m)`, say, from being `∅` in general — only used in the "neither
decider fires" branch, to show the bisection's two halves are each individually `≠ ∅`, matching that
branch's `A ∩ Xn ≠ ∅ ↔ .1 ≠ ∅`/`A \ Xn ≠ ∅ ↔ .2 ≠ ∅` obligations). The two decider-fires branches
need no such hypothesis at all — `.1`/`.2` there are literally `∅`/`B'`, and the requisite `↔`s
reduce to `hAB` via the algebraic facts `A ∩ Xn = ∅ → A \ Xn = A` (resp. `A \ Xn = ∅ → A ∩ Xn = A`).
The "not presented" branch reduces to exactly `splitChoice'_isSplitSpec` (`Exercise812c.lean`),
verbatim. -/
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
    · by_cases h2 : emptyDiffDec P hDiff (Nat.pair n k) = 1
      · have hDiffEmpty : P.X n \ P.X k = ∅ :=
          (emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mp h2
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
          fun he => h2 ((emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mpr he)
        rw [ite_eq_right h1, ite_eq_right h2]
        exact ⟨Or.inr (Q.mem_X _), Or.inr (Q.mem_X _), iff_of_false h1' (hQne _),
          iff_of_false h2' (hQne _), B.union m, B.disjoint m⟩
  · unfold splitFromBisection
    rw [dite_eq_right h]
    exact splitChoice'_isSplitSpec W hWnomin hAB hBW Xn

end splitFromBisection
end ComputableBisection
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **`8.12(g)(3)`, `V`-as-prober half**: `splitX812f` also satisfies `SplitSpec'`, the mirror
image of `Exercise812eD.lean`'s `hxSplit812e`. The extra hypothesis it needs, `∀ j, UX j ≠ ∅`, is
immediate from `U_mem_UX`/`U.mem`'s own `X.Nonempty` conjunct (`Definition87.lean` line 96). -/
theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection.isSplitSpec' VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Uunion

open Domain.Recursive NeighborhoodSystem

/-- **`Uunion n m` genuinely indexes `UX n ∪ UX m`** — mirrors `Udiff.spec`'s shape exactly, but the
hypothesis is never used (the union is already unconditionally genuine, `U_union_mem`): the raw
`appendListCode` output is already a genuine `U`-neighbourhood, so re-canonicalizing it (`canonCode`'s
own lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion.eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion.eq_union]

end Uunion
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **`8.12(g)(3)`, `U`-as-prober half**: `splitX812e` also satisfies `SplitSpec'` — completing the
concrete-construction half of `8.12(g)(3)` left open by `Exercise812e.lean`'s generic
`splitFromBisection.isSplitSpec'`. The extra hypothesis it needs, `∀ j, VX j ≠ ∅`, is immediate:
every `VX j` is `V.mem`-genuine (`VComputablePresentation.mem_X`) and `V.mem` structurally excludes
`∅` (`V.mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty`, `Exercise812.lean` line 199). -/
theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection.isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed (fun j => (VX_nonempty j).ne_empty)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `𝒰` — via `U_surj_UX` on
`U_union_UX_mem` (mirroring `U_diff_iff_nonempty`'s use of `U_surj_UX`, but unconditional). -/
theorem U_union_exists (n m : ℕ) : ∃ k, UX k = UX n ∪ UX m := U_surj_UX (U_union_UX_mem n m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`∪`, for `𝒰`**: trivially recursively decidable (the always-`1` constant), since
`U_union_exists` shows the underlying predicate is unconditionally `True`. -/
theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion.primrec
  unionIdx_spec := Uunion.spec
  union_computable := U_union_computable

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet.union_same_level` at differing levels** — the bitwise-`OR`
analogue of `levelSet.myInter`, mirroring its proof verbatim with `myLor`/`Nat.testBit_or` in place
of `myLand`/`Nat.testBit_and`. -/
theorem myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet.union_same_level, myLor_eq_lor]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- **`VunionRaw` realizes `VX n ∪ VX m`** at the `levelSet` level (unconditionally). -/
theorem VunionRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Vunion

open Domain.Recursive NeighborhoodSystem

/-- **`Vunion n m` genuinely indexes `VX n ∪ VX m`**, unconditionally — `VunionRaw n m` is already
non-empty (both `VX n`, `VX m` are non-empty, `VX_nonempty`, and a union of a non-empty set with
anything is non-empty), so `canonIdx` is a no-op on it (`canonIdx.eq_self_of_nonempty`), mirroring
`Vinter_spec`'s shape but with the hypothesis discharged internally rather than assumed. -/
theorem spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VunionRaw]

end Vunion
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Vunion

open Domain.Recursive NeighborhoodSystem

/-- `Vunion.spec`, repackaged to accept (and discard) `IsComputableUnion`'s hypothesis. -/
theorem spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion.spec n m

end Vunion
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion.spec n m⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`∪`, for `V`**: trivially recursively decidable (the always-`1` constant). -/
theorem V_union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V_union_exists t.unpair.1 t.unpair.2) rfl⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open Domain.Recursive NeighborhoodSystem

/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hY0`: index `0` presents `V`'s master neighbourhood. `Nat.unpair 0 = (0, 0)` and
`levelSet 0 0 = ∅`, so `canonIdx 0` falls back to `VmasterIdx = Nat.pair 0 1`
(`canonIdx.eq_master_of_empty`), whose `VX`-image is `V.master` (`VX_VmasterIdx`). -/
theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx.eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet.zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_e_d : @DomainTheory.NeighbourhoodSystems.SplitSpec' Rat Nat DomainTheory.NeighbourhoodSystems.V
  DomainTheory.NeighbourhoodSystems.splitX812e :=
  @DomainTheory.NeighbourhoodSystems.hxSplit812e

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_f : @DomainTheory.NeighbourhoodSystems.SplitSpec' Nat Rat DomainTheory.NeighbourhoodSystems.U
  DomainTheory.NeighbourhoodSystems.splitX812f :=
  @DomainTheory.NeighbourhoodSystems.hySplit812f

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_g1a : @Eq (Set Rat) (DomainTheory.NeighbourhoodSystems.UX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Rat DomainTheory.NeighbourhoodSystems.U) :=
  DomainTheory.NeighbourhoodSystems.UX_zero

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_g1b : @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Nat DomainTheory.NeighbourhoodSystems.V) :=
  DomainTheory.NeighbourhoodSystems.VX_zero

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion.spec'

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
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

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open Domain.Recursive NeighborhoodSystem

theorem Vunion : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vunion t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VunionRaw).of_eq fun _ => rfl

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `∪`.** -/
def V_isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec.Vunion
  unionIdx_spec := Vunion.spec'
  union_computable := V_union_computable

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem Exercise718

/-- **Exercise 8.12, completed in full**: `U` and `V` are effectively isomorphic
neighbourhood systems. -/
noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V_isComputableDiff splitX812e isComputableSplit.«812e» splitX812f isComputableSplit.«812f»
    U_isPositive U_diffClosed U_noMinimal hxSplit812e V_isPositive V_diffClosed V_noMinimal
    hySplit812f U_master_nonempty V_master_nonempty U_isComputableUnion V_isComputableUnion UX_zero
    VX_zero

end DomainTheory.NeighbourhoodSystems
