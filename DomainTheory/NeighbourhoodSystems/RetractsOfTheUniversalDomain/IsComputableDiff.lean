module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

structure IsComputableDiff {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V) where
  diffIdx : ℕ → ℕ → ℕ
  diffIdx_primrec : Nat.Primrec (fun t => diffIdx t.unpair.1 t.unpair.2)
  diffIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n \ P.X m) → P.X (diffIdx n m) = P.X n \ P.X m
  diff_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n \ P.X m)

namespace IsComputableDiff

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
variable (hDiff : IsComputableDiff P)

theorem exists_iff_ne_empty (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    (∃ k, P.X k = P.X n \ P.X m) ↔ P.X n \ P.X m ≠ ∅ := by
  constructor
  · rintro ⟨k, hk⟩ hempty
    exact NoMinimal.mem_ne_empty hnomin (P.mem_X k) (hk.trans hempty)
  · intro hne
    rcases hdiff (P.mem_X n) (P.mem_X m) with hempty | hmem
    · exact absurd hempty hne
    · exact P.surj hmem

noncomputable def existsDiffDec : ℕ → ℕ := fun t => isOne (hDiff.diff_computable.choose t)

namespace existsDiffDec

theorem le_one (t : ℕ) : existsDiffDec P hDiff t ≤ 1 := isOne_le_one _

theorem spec (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 1 ↔ ∃ k, P.X k = P.X n \ P.X m := by
  unfold existsDiffDec
  rw [isOne_eq_one_iff]
  have h := hDiff.diff_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem eq_zero_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 0 ↔ P.X n \ P.X m = ∅ := by
  have hle := existsDiffDec.le_one P hDiff (Nat.pair n m)
  have h1 := existsDiffDec.spec P hDiff n m
  have h2 := exists_iff_ne_empty P hdiff hnomin n m
  constructor
  · intro h0
    by_contra hne
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := h1.mpr (h2.mpr hne)
    omega
  · intro hempty
    by_contra hne0
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := by omega
    exact (h2.mp (h1.mp h1')) hempty

end existsDiffDec

noncomputable def emptyDiffDec : ℕ → ℕ := fun t => 1 - existsDiffDec P hDiff t

namespace emptyDiffDec

theorem le_one (t : ℕ) : emptyDiffDec P hDiff t ≤ 1 := by
  unfold emptyDiffDec; have := existsDiffDec.le_one P hDiff t; omega

theorem eq_one_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyDiffDec P hDiff (Nat.pair n m) = 1 ↔ P.X n \ P.X m = ∅ := by
  unfold emptyDiffDec
  have hle := existsDiffDec.le_one P hDiff (Nat.pair n m)
  have h0 := existsDiffDec.eq_zero_iff P hDiff hdiff hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

end emptyDiffDec

namespace primrec

theorem existsDiffDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.existsDiffDec P hDiff) :=
  (primrec_isOne.comp hDiff.diff_computable.choose_spec.1).of_eq fun _ => rfl

theorem emptyDiffDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P hDiff) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec.existsDiffDec P hDiff)

end primrec

end IsComputableDiff

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

noncomputable def existsInterDec : ℕ → ℕ := fun t => isOne (P.cons_computable.choose t)

namespace existsInterDec

theorem le_one (t : ℕ) : existsInterDec P t ≤ 1 := isOne_le_one _

theorem spec (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
  unfold existsInterDec
  rw [isOne_eq_one_iff]
  have h := P.cons_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem eq_zero_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 0 ↔ P.X n ∩ P.X m = ∅ := by
  have hle := existsInterDec.le_one P (Nat.pair n m)
  constructor
  · intro h0
    by_contra hne
    have hmem : V.mem (P.X n ∩ P.X m) :=
      (hpos (P.mem_X n) (P.mem_X m)).mpr (Set.nonempty_iff_ne_empty.mpr hne)
    obtain ⟨k, hk⟩ := P.surj hmem
    have h1 : existsInterDec P (Nat.pair n m) = 1 :=
      (existsInterDec.spec P n m).mpr ⟨k, by rw [hk]⟩
    omega
  · intro hempty
    by_contra hne1
    have h1 : existsInterDec P (Nat.pair n m) = 1 := by omega
    obtain ⟨k, hk⟩ := (existsInterDec.spec P n m).mp h1
    exact absurd (Set.subset_eq_empty hk hempty) (hnomin.mem_ne_empty (P.mem_X k))

end existsInterDec

noncomputable def emptyInterDec : ℕ → ℕ := fun t => 1 - existsInterDec P t

namespace emptyInterDec

theorem le_one (t : ℕ) : emptyInterDec P t ≤ 1 := by
  unfold emptyInterDec; have := existsInterDec.le_one P t; omega

theorem eq_one_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyInterDec P (Nat.pair n m) = 1 ↔ P.X n ∩ P.X m = ∅ := by
  unfold emptyInterDec
  have hle := existsInterDec.le_one P (Nat.pair n m)
  have h0 := existsInterDec.eq_zero_iff P hpos hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

end emptyInterDec

namespace primrec

theorem existsInterDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.existsInterDec P) :=
  (primrec_isOne.comp P.cons_computable.choose_spec.1).of_eq fun _ => rfl

theorem emptyInterDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec.existsInterDec P)

end primrec

end DomainTheory.NeighbourhoodSystems
