module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

structure ComputableBisection {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W) where
  left : ℕ → ℕ
  right : ℕ → ℕ
  left_primrec : Nat.Primrec left
  right_primrec : Nat.Primrec right
  disjoint : ∀ k, Q.X (left k) ∩ Q.X (right k) = ∅
  union : ∀ k, Q.X (left k) ∪ Q.X (right k) = Q.X k
  left_congr : ∀ k k', Q.X k = Q.X k' → Q.X (left k) = Q.X (left k')
  right_congr : ∀ k k', Q.X k = Q.X k' → Q.X (right k) = Q.X (right k')

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

open scoped Classical in
noncomputable def splitFromBisection (A : Set α) (B' : Set γ) (Xn : Set α) : Set γ × Set γ :=
  if h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k then
    if emptyInterDec P (Nat.pair h.choose h.choose_spec.choose_spec.choose) = 1 then
      (∅, B')
    else if IsComputableDiff.emptyDiffDec P hDiff (Nat.pair h.choose h.choose_spec.choose_spec.choose) = 1 then
      (B', ∅)
    else
      (Q.X (B.left h.choose_spec.choose), Q.X (B.right h.choose_spec.choose))
  else
    splitChoice' W hWnomin A B' Xn

noncomputable def negIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k)) m (B.right m))

noncomputable def posIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k)) m (B.left m))

namespace emptyDiffDec

theorem congr {n n' k k' : ℕ} (hdiffClosed : V.DiffClosed) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) =
      IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n' k') := by
  have h1 := IsComputableDiff.emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k
  have h2 := IsComputableDiff.emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n' k'
  rw [hn, hk] at h1
  have hiff : IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) = 1 ↔
      IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := IsComputableDiff.emptyDiffDec.le_one P hDiff (Nat.pair n k)
  have hle2 := IsComputableDiff.emptyDiffDec.le_one P hDiff (Nat.pair n' k')
  omega

end emptyDiffDec

namespace emptyInterDec

theorem congr {n n' k k' : ℕ} (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyInterDec P (Nat.pair n k) = emptyInterDec P (Nat.pair n' k') := by
  have h1 := emptyInterDec.eq_one_iff P hpos hnomin n k
  have h2 := emptyInterDec.eq_one_iff P hpos hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyInterDec P (Nat.pair n k) = 1 ↔ emptyInterDec P (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyInterDec.le_one P (Nat.pair n k)
  have hle2 := emptyInterDec.le_one P (Nat.pair n' k')
  omega

end emptyInterDec

namespace splitFromBisection

theorem eq (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (n m k : ℕ) :
    splitFromBisection P hDiff B hWnomin (P.X n) (Q.X m) (P.X k) =
      if emptyInterDec P (Nat.pair n k) = 1 then (∅, Q.X m)
      else if IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) = 1 then (Q.X m, ∅)
      else (Q.X (B.left m), Q.X (B.right m)) := by
  have hex : ∃ n' m' k', P.X n = P.X n' ∧ Q.X m = Q.X m' ∧ P.X k = P.X k' :=
    ⟨n, m, k, rfl, rfl, rfl⟩
  obtain ⟨hn', hm', hk'⟩ := hex.choose_spec.choose_spec.choose_spec
  have hInterEq : emptyInterDec P (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      emptyInterDec P (Nat.pair n k) := (emptyInterDec.congr P hpos hnomin hn' hk').symm
  have hDiffEq : IsComputableDiff.emptyDiffDec P hDiff
      (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) :=
    (emptyDiffDec.congr P hDiff hdiffClosed hnomin hn' hk').symm
  unfold splitFromBisection
  rw [dite_eq_left hex, hInterEq, hDiffEq]
  split_ifs with h1 h2
  · rfl
  · rfl
  · have hl := (B.left_congr m hex.choose_spec.choose hm').symm
    have hr := (B.right_congr m hex.choose_spec.choose hm').symm
    rw [hl, hr]

end splitFromBisection

namespace primrec

theorem negIdxFromBisection :
    Nat.Primrec (fun t => negIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P hDiff
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (IsComputableDiff.primrec.emptyDiffDec P hDiff).comp hnk
  have hright : Nat.Primrec (fun t : ℕ => B.right t.unpair.2.unpair.1) := B.right_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P hDiff
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.right t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hright
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

theorem posIdxFromBisection :
    Nat.Primrec (fun t => posIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P hDiff
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (IsComputableDiff.primrec.emptyDiffDec P hDiff).comp hnk
  have hleft : Nat.Primrec (fun t : ℕ => B.left t.unpair.2.unpair.1) := B.left_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P hDiff
        (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.left t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hleft
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

end primrec

namespace isComputableSplit

noncomputable def ofBisection (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) :
    IsComputableSplit P Q (splitFromBisection P hDiff B hWnomin) where
  posIdx := posIdxFromBisection P hDiff B
  negIdx := negIdxFromBisection P hDiff B
  posIdx_primrec := primrec.posIdxFromBisection P hDiff B
  negIdx_primrec := primrec.negIdxFromBisection P hDiff B
  posIdx_spec n m k hne := by
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2]
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      have h2' : IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := IsComputableDiff.emptyDiffDec.le_one P hDiff (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2']
  negIdx_spec n m k hne := by
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · simp [negIdxFromBisection, h1]
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      have h2' : IsComputableDiff.emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := IsComputableDiff.emptyDiffDec.le_one P hDiff (Nat.pair n k); omega
      simp [negIdxFromBisection, h1', h2']

end isComputableSplit

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
