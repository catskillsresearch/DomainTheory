module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)


noncomputable def YFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1.unpair.1
  let bx := w.unpair.1.unpair.2
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  selectFn (yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (hUnion0.unionIdx acc.unpair.2
        (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))
      (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))

noncomputable def YFoldInnerPair (nb N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion0 (Nat.pair nb (Nat.pair i acc)))

theorem YFoldStep_eq (n bx i acc : ℕ) :
    YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair (Nat.pair n bx) (Nat.pair i acc)) =
      selectFn (yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (hUnion0.unionIdx acc.unpair.2
            (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))
          (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx))) := by
  unfold YFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

end YPseqCode

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

noncomputable def YFoldInner (n bx N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion0 (Nat.pair (Nat.pair n bx) (Nat.pair i acc)))

end YPseqCode

namespace YFoldInner
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem eq_pair (n bx N : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N =
      YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair n bx) N := rfl

theorem succ (n bx N : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx (N + 1) =
      YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair (Nat.pair n bx) (Nat.pair N (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX
          splitY hSplitY hUnion0 n bx N))) := rfl

theorem zero (n bx : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx 0 =
      Nat.pair 0 0 := rfl

theorem found_le_one {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
      ≤ 1 := by
  intro N
  induction N with
  | zero => simp [YFoldInner.zero]
  | succ N ih =>
    rw [YFoldInner.succ, YFoldStep_eq]
    rcases yPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

theorem found_iff {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      ↔ ∃ i < N, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 := by
  intro N
  induction N with
  | zero => simp [YFoldInner.zero]
  | succ N ih =>
    rw [YFoldInner.succ, YFoldStep_eq]
    rcases yPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
          (Nat.pair 1 (hUnion0.unionIdx
            (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.2
            (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx)))
          (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx))
          ).unpair.1 = 1 := by
        have hle := YFoldInner.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hUnion0 hbx n N
        rcases Nat.eq_zero_or_pos
            (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
          with hf | hf
        · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

end YPseqCode

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin in

theorem mem_of_found {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      → D₀.mem (P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        n bx N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [YFoldInner.zero] at h
  | succ N ih =>
    intro hfound1
    rw [YFoldInner.succ, YFoldStep_eq] at hfound1 ⊢
    rcases yPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := YFoldInner.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        hbx n N
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact yPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
      · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := yPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
        have hex : ∃ k, P₀.X k =
            P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
              ).unpair.2 ∪
              P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx) :=
          P₀.surj (NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem)
        rw [hUnion0.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

end YPseqCode

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin in

theorem mem_iff {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      → ∀ z : α, z ∈ P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          n bx N).unpair.2 ↔
        ∃ i < N, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 ∧
          z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) := by
  intro N
  induction N with
  | zero => intro h; simp [YFoldInner.zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [YFoldInner.succ, YFoldStep_eq] at hfound1 ⊢
    rcases yPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := YFoldInner.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        hbx n N
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((YFoldInner.found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hUnion0 hbx n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := YFoldInner.mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₀pos hD₀diff hD₀nomin hUnion0 hbx n N hf1
        have hnewmem := yPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
        have hex : ∃ k, P₀.X k =
            P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
              ).unpair.2 ∪
              P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx) :=
          P₀.surj (NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem)
        rw [hUnion0.unionIdx_spec hex, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

end YPseqCode

end YFoldInner

end DomainTheory.NeighbourhoodSystems
