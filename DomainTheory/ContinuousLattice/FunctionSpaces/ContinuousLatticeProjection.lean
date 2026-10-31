module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetraction

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Finset

variable {D : Type u} {D' : Type v}
variable [CompleteLattice D] [CompleteLattice D']

structure ContinuousLatticeProjection (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D']
    extends ContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d,
    @LE.le D'
      (ChainCompletePartialOrder.instOfCompleteLattice (α := D')).toPartialOrder.toPreorder.toLE
      (incl (retr d)) d

namespace ContinuousLatticeProjection

theorem retr_bot (P : ContinuousLatticeProjection D D') : (P.retr : D' → D) ⊥ = ⊥ := by
  have hle : (⊥ : D') ≤ P.incl (⊥ : D) := bot_le
  have heq : (P.retr : D' → D) (P.incl (⊥ : D)) = (⊥ : D) := P.retr_incl (d := (⊥ : D))
  exact le_antisymm (le_trans (P.retr.monotone hle) (le_of_eq heq)) bot_le

theorem incl_bot (P : ContinuousLatticeProjection D D') : P.incl (⊥ : D) = ⊥ :=
  le_antisymm (by simpa [retr_bot P] using P.incl_retr_le (⊥ : D')) bot_le

theorem retr_eq_sSup (P : ContinuousLatticeProjection D D') (x' : D') :
    (P.retr : D' → D) x' = sSup {x | (P.incl : D → D') x ≤ x'} := by
  apply le_antisymm
  · exact le_sSup (show (P.incl : D → D') (P.retr x') ≤ x' from P.incl_retr_le x')
  · refine sSup_le fun x hx => ?_
    calc x = (P.retr : D' → D) (P.incl x) := (P.retr_incl x).symm
      _ ≤ (P.retr : D' → D) x' := P.retr.monotone hx

theorem incl_wayBelow (P : ContinuousLatticeProjection D D') (hD' : ContinuousLattice D')
    {x y : D} (h : x ≪ y) : @WayBelow D' _ (P.incl x) (P.incl y) := by
  set W : Set D' := { z' | @WayBelow D' _ z' (P.incl y) }
  have hWne : W.Nonempty := ⟨(⊥ : D'), @WayBelow.bot D' _ (P.incl y)⟩
  have hWdir : DirectedOn (· ≤ ·) W := by
    intro p hp q hq
    exact ⟨p ⊔ q, @WayBelow.sup D' _ p q (P.incl y) hp hq, le_sup_left, le_sup_right⟩
  have hy : y = sSup (Set.image (P.retr : D' → D) W) := by
    rw [← P.retr.preservesDirectedSup_coe W hWne hWdir, hD'.sSup_wayBelow (P.incl y),
      P.retr_incl y]
  have hImgne : (Set.image (P.retr : D' → D) W).Nonempty := by
    obtain ⟨z', hz'⟩ := hWne
    exact ⟨P.retr z', z', hz', rfl⟩
  have hImgdir : DirectedOn (· ≤ ·) (Set.image (P.retr : D' → D) W) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨P.retr (a ⊔ b), ⟨a ⊔ b, @WayBelow.sup D' _ a b (P.incl y) ha hb, rfl⟩, ?_, ?_⟩
    · exact P.retr.monotone le_sup_left
    · exact P.retr.monotone le_sup_right
  have hx : x ≪ sSup (Set.image (P.retr : D' → D) W) := by rwa [← hy]
  obtain ⟨prz, hprz, hxpr⟩ := (WayBelow.sSup_iff hImgne hImgdir).1 hx
  obtain ⟨z', hz', rfl⟩ := hprz
  exact @WayBelow.le_trans D' _ (P.incl x) z' (P.incl y)
    (le_trans (P.incl.monotone hxpr.le) (P.incl_retr_le z')) hz'

theorem incl_injective (P : ContinuousLatticeProjection D D') {x y : D} (h : P.incl x = P.incl y) :
    x = y := by
  rw [← P.retr_incl x, ← P.retr_incl y, h]

theorem incl_sup (P : ContinuousLatticeProjection D D') (x y : D) :
    P.incl (x ⊔ y) = P.incl x ⊔ P.incl y := by
  apply le_antisymm
  · have hx : x ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl x).symm) (P.retr.monotone le_sup_left)
    have hy : y ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl y).symm) (P.retr.monotone le_sup_right)
    exact le_trans (P.incl.monotone (sup_le hx hy)) (P.incl_retr_le (P.incl x ⊔ P.incl y))
  · exact sup_le (P.incl.monotone le_sup_left) (P.incl.monotone le_sup_right)

theorem incl_finset_sup (P : ContinuousLatticeProjection D D') (T : Finset D) :
    P.incl (T.sup (fun x => x)) = T.sup (fun x => P.incl x) := by
  classical
  refine Finset.induction_on T ?base ?step
  · simp only [sup_empty]
    exact incl_bot P
  · intro a s _ ih
    simp only [sup_insert]
    rw [incl_sup P, ih]

def finsetSupOf (S : Set D) : Set D :=
  { z | ∃ T : Finset D, (∀ x ∈ T, x ∈ S) ∧ z = T.sup id }

theorem directedOn_finsetSupOf (S : Set D) :
    DirectedOn (· ≤ ·) (finsetSupOf S) := by
  classical
  intro a ha b hb
  obtain ⟨T₁, hT₁, rfl⟩ := ha
  obtain ⟨T₂, hT₂, rfl⟩ := hb
  have hunion : (T₁ ∪ T₂).sup id = T₁.sup id ⊔ T₂.sup id := by
    simpa using Finset.sup_union (s₁ := T₁) (s₂ := T₂) (f := id)
  refine ⟨T₁.sup id ⊔ T₂.sup id, ⟨T₁ ∪ T₂, ?_, hunion.symm⟩, le_sup_left, le_sup_right⟩
  intro x hx
  simp only [Finset.mem_union] at hx
  exact hx.elim (hT₁ x) (hT₂ x)

theorem mem_finsetSupOf_of_mem {S : Set D} {x : D} (hx : x ∈ S) :
    x ∈ finsetSupOf S :=
  ⟨{x}, by simp [hx], by simp⟩

theorem sSup_le_finsetSupOf (S : Set D) : sSup (finsetSupOf S) ≤ sSup S :=
  sSup_le fun z hz => by
    obtain ⟨T, hTS, rfl⟩ := hz
    exact Finset.sup_le fun t ht => le_sSup (hTS t ht)

theorem le_sSup_finsetSupOf (S : Set D) : sSup S ≤ sSup (finsetSupOf S) :=
  sSup_le fun _ hx => le_sSup (mem_finsetSupOf_of_mem hx)

theorem sSup_finsetSupOf (S : Set D) : sSup S = sSup (finsetSupOf S) :=
  le_antisymm (le_sSup_finsetSupOf S) (sSup_le_finsetSupOf S)

theorem incl_sSup (P : ContinuousLatticeProjection D D') (S : Set D) :
    P.incl (sSup S) = sSup (Set.image (P.incl : D → D') S) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    simp only [sSup_empty, Set.image_empty, incl_bot P]
  · rw [sSup_finsetSupOf S]
    have hdir := directedOn_finsetSupOf S
    have hne : (finsetSupOf S).Nonempty := by
      obtain ⟨x, hx⟩ := hS
      exact ⟨x, mem_finsetSupOf_of_mem hx⟩
    rw [P.incl.preservesDirectedSup_coe (finsetSupOf S) hne hdir]
    apply le_antisymm
    · apply sSup_le
      intro b hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨T, hT, rfl⟩ := hz
      have h := incl_finset_sup P T
      conv_lhs => rw [show T.sup id = T.sup (fun x => x) from rfl]
      rw [h]
      apply Finset.sup_le
      intro t ht
      exact le_sSup (Set.mem_image_of_mem (P.incl : D → D') (hT t ht))
    · apply sSup_le
      intro b hb
      obtain ⟨x, hxS, rfl⟩ := (Set.mem_image (P.incl : D → D') S b).1 hb
      exact le_sSup (Set.mem_image_of_mem (P.incl : D → D') (mem_finsetSupOf_of_mem hxS))

theorem incl_sup_of_preservesSSup (i : D → D') (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (x y : D) :
    i (x ⊔ y) = i x ⊔ i y := by
  calc i (x ⊔ y) = i (sSup {x, y}) := by rw [sSup_pair]
    _ = sSup (i '' {x, y}) := hi _
    _ = sSup {i x, i y} := by rw [Set.image_pair]
    _ = i x ⊔ i y := sSup_pair

theorem incl_mono_of_preservesSSup (i : D → D') (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) :
    Monotone i := by
  intro x y hxy
  have h := incl_sup_of_preservesSSup i hi x y
  rw [sup_eq_right.mpr hxy] at h
  rw [h]; exact le_sup_left

theorem le_of_incl_le (i : D → D') (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) {x y : D} (h : i x ≤ i y) : x ≤ y := by
  have h1 : i (x ⊔ y) = i y := by rw [incl_sup_of_preservesSSup i hi, sup_eq_right.mpr h]
  exact sup_eq_right.mp (hinj h1)

end ContinuousLatticeProjection

end DomainTheory.ContinuousLattice
