module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.deltaPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

noncomputable def XFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  selectFn (xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (hUnion1.unionIdx acc.unpair.2
        (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))
      (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))

theorem XFoldStep_eq (n i acc : ℕ) :
    XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        (Nat.pair n (Nat.pair i acc)) =
      selectFn (xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (hUnion1.unionIdx acc.unpair.2
            (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))
          (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))) := by
  unfold XFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

end XPseqCode

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

noncomputable def XFold (n N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion1 (Nat.pair n (Nat.pair i acc)))

end XPseqCode

namespace XFold
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem succ (n N : ℕ) :
    XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (N + 1) =
      XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        (Nat.pair n (Nat.pair N (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          n N))) := rfl

theorem zero (n : ℕ) : XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n 0 =
    Nat.pair 0 0 := rfl

theorem found_le_one (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [XFold.zero]
  | succ N ih =>
    rw [XFold.succ, XFoldStep_eq]
    rcases xPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

theorem found_iff (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 ↔
      ∃ i < N, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  intro N
  induction N with
  | zero => simp [XFold.zero]
  | succ N ih =>
    rw [XFold.succ, XFoldStep_eq]
    rcases xPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          (Nat.pair 1 (hUnion1.unionIdx
            (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2
            (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N)))
          (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N))
          ).unpair.1 = 1 := by
        have hle := XFold.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
        rcases Nat.eq_zero_or_pos
            (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
          hf | hf
        · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

end XPseqCode

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

include hD₁pos hD₁diff hD₁nomin in

theorem mem_of_found (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      D₁.mem (P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold.zero] at h
  | succ N ih =>
    intro hfound1
    rw [XFold.succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact xPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := xPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

end XPseqCode

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

include hD₁pos hD₁diff hD₁nomin in

theorem mem_iff (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      ∀ z : β, z ∈ P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ↔
        ∃ i < N, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∧
          z ∈ P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold.zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [XFold.succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk.zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold.found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((XFold.found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hUnion1 n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := XFold.mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₁pos hD₁diff hD₁nomin hUnion1 n N hf1
        have hnewmem := xPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex, Set.mem_union, ih hf1 z]
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

end XPseqCode

end XFold

end DomainTheory.NeighbourhoodSystems
