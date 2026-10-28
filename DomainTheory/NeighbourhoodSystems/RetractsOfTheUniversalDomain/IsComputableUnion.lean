module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

structure IsComputableUnion {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    where

  unionIdx : ℕ → ℕ → ℕ

  unionIdx_primrec : Nat.Primrec (fun t => unionIdx t.unpair.1 t.unpair.2)

  unionIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n ∪ P.X m) → P.X (unionIdx n m) = P.X n ∪ P.X m

  union_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n ∪ P.X m)

theorem NeighborhoodSystem.mem_union_of_mem {γ : Type*} {D : NeighborhoodSystem γ}
    (hpos : D.IsPositive) (hdiff : D.DiffClosed) (hnomin : D.NoMinimal) {X Y : Set γ}
    (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∪ Y) :=
  (union.mem_or_empty hpos hdiff (Or.inr hX) (Or.inr hY)).resolve_left fun h =>
    hnomin.mem_ne_empty hX (Set.subset_eq_empty Set.subset_union_left h)

namespace IsComputableUnion

noncomputable def combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) (r0 r1 : ℕ) : ℕ :=
  selectFn r0.unpair.1
    (selectFn r1.unpair.1 (Nat.pair 1 (hUnion.unionIdx r0.unpair.2 r1.unpair.2)) r0)
    r1

namespace combineFound2
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem found_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 ↔ r0.unpair.1 = 1 ∨ r1.unpair.1 = 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; omega
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]; omega

theorem mem_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2))
    (hfound : (combineFound2 hUnion r0 r1).unpair.1 = 1) (z : γ) :
    z ∈ Q.X (combineFound2 hUnion r0 r1).unpair.2 ↔
      (r0.unpair.1 = 1 ∧ z ∈ Q.X r0.unpair.2) ∨ (r1.unpair.1 = 1 ∧ z ∈ Q.X r1.unpair.2) := by
  unfold combineFound2 at hfound ⊢
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero] at hfound ⊢
    constructor
    · intro hz; exact Or.inr ⟨hfound, hz⟩
    · rintro (⟨h, -⟩ | ⟨-, hz⟩)
      · omega
      · exact hz
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one] at hfound ⊢
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero] at hfound ⊢
      constructor
      · intro hz; exact Or.inl ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨h, -⟩)
        · exact hz
        · omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · exact Or.inl ⟨by omega, hz⟩
        · exact Or.inr ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨-, hz⟩)
        · exact Or.inl hz
        · exact Or.inr hz

theorem mem_of_found {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2)) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 →
      W.mem (Q.X (combineFound2 hUnion r0 r1).unpair.2) := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]
    exact hmem1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]
      exact fun _ => hmem0'
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      intro _
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex]
      exact NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1'

theorem found_le_one {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 ≤ 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; exact h1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; exact h0
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]

end combineFound2

end IsComputableUnion

end DomainTheory.NeighbourhoodSystems
