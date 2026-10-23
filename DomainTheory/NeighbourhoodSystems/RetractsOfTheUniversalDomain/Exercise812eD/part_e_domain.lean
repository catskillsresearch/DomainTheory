module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`B812e`: `V`'s computable canonical bisection, packaged as a `ComputableBisection`.** -/
def B812e : ComputableBisection VComputablePresentation where
  left := splitVLeft
  right := splitVRight
  left_primrec := primrec_splitVLeft
  right_primrec := primrec_splitVRight
  disjoint := splitV_disjoint
  union := splitV_union
  left_congr := fun _ _ h => splitVLeft_congr h
  right_congr := fun _ _ h => splitVRight_congr h

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The difference index: `diffCode` on canonicalized codes (`UX` re-canonicalizes on lookup, so no
further canonicalization is needed here — mirrors `Uinter`). -/
def Udiff (n m : ℕ) : ℕ := diffCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, exactly mirroring
`U_cons_iff_nonempty_inter`: `U_diff_mem` (`Exercise812c.lean`) shows `UX n \ UX m` is always either
empty or a genuine `U`-neighbourhood, and every `UX k` is non-empty (`U.mem` forces
`Set.Nonempty`), so "presentable" and "non-empty" coincide. -/
theorem U_diff_iff_nonempty (n m : ℕ) :
    (∃ k, UX k = UX n \ UX m) ↔ (UX n \ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact (U_mem_UX k).2.1
  · intro hne
    rcases U_diff_mem (U_mem_UX n) (U_mem_UX m) with hempty | hmem
    · exact absurd hempty hne.ne_empty
    · exact U_surj_UX hmem

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Udiff

open Domain.Recursive NeighborhoodSystem

/-- **`Udiff` realizes set difference at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — the one respect in which `\` is *simpler* than `∩` here (no consistency case
split needed at this stage). -/
theorem eq_diff (n m : ℕ) :
    presentedIntervals (decodeQPairList (Udiff n m)) = UX n \ UX m := by
  unfold Udiff
  exact presentedIntervals_decodeQPairList_diffCode (canonCode n) (canonCode m)

end Udiff
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Udiff

open Domain.Recursive NeighborhoodSystem

theorem primrec : Nat.Primrec (fun t : ℕ => Udiff t.unpair.1 t.unpair.2) := by
  unfold Udiff
  exact (primrec_diffCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Udiff
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`\`, for `𝒰`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable — mirrors
`U_cons_computable` exactly, substituting `Udiff` for the raw `combineCode` composite. -/
theorem U_diff_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n \ UX m) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp Udiff.primrec)
  show (∃ k, UX k = UX t.unpair.1 \ UX t.unpair.2) ↔ _
  rw [U_diff_iff_nonempty, ← Udiff.eq_diff]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace Udiff

open Domain.Recursive NeighborhoodSystem

/-- **`Udiff n m` genuinely indexes `UX n \ UX m` whenever that difference is a genuine
neighbourhood** — mirrors `Uinter_spec` exactly: the raw `diffCode` output is already a genuine
`U`-neighbourhood (by hypothesis via `Udiff.eq_diff`), so re-canonicalizing it (`canonCode`'s own
lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem spec {n m : ℕ} (h : ∃ k, UX k = UX n \ UX m) : UX (Udiff n m) = UX n \ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Udiff n m))) := by
    rw [Udiff.eq_diff]
    obtain ⟨k, hk⟩ := h
    rw [← hk]; exact U_mem_UX k
  show presentedIntervals (decodeQPairList (canonCode (Udiff n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Udiff.eq_diff]

end Udiff
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U` has a computable `\`**, completing the missing prerequisite this section opened with. -/
def U_isComputableDiff : IsComputableDiff UComputablePresentation where
  diffIdx := Udiff
  diffIdx_primrec := Udiff.primrec
  diffIdx_spec := Udiff.spec
  diff_computable := U_diff_computable

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitX812e`: the exercise's literal target split**, `U` as prober against `V`'s canonical
bisection. -/
noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V_noMinimal

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace isComputableSplit

open Domain.Recursive NeighborhoodSystem

/-- **Exercise 8.12(e), completed in full**: `splitX812e` satisfies `IsComputableSplit`.
`noncomputable def`, not `theorem` — `IsComputableSplit` is a data-carrying structure (its
`posIdx`/`negIdx` fields are `ℕ`-valued functions), mirroring `isComputableSplit.ofBisection`
itself (`(e)(c)(ii)`). -/
noncomputable def «812e» :
    IsComputableSplit UComputablePresentation VComputablePresentation splitX812e :=
  ComputableBisection.isComputableSplit.ofBisection UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed

end isComputableSplit
end DomainTheory.NeighbourhoodSystems
