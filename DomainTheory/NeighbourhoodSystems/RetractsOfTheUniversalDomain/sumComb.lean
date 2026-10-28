module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

noncomputable def sumComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  (cond U).comp
    ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
        (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
      jPlus)

theorem toElementMap_bot_eq_bot_of_comp_eq_idMap {α β : Type*} {D : NeighborhoodSystem α}
    {E : NeighborhoodSystem β} {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) : j.toElementMap E.bot = D.bot := by
  apply le_antisymm
  · have h2 := j.toElementMap_mono (E.bot_le (i.toElementMap D.bot))
    rwa [toElementMap_of_comp_eq_idMap hji] at h2
  · exact D.bot_le _

theorem jPlus_bot_eq_bot :
    jPlus.toElementMap U.bot = (sum U U U_mem_nonempty U_mem_nonempty).bot :=
  toElementMap_bot_eq_bot_of_comp_eq_idMap jPlus_comp_iPlus

theorem fixedNbhd_mem_nonempty (a : ApproximableMap U U) :
    ∀ X, (fixedNbhd a).mem X → X.Nonempty :=
  fun X hX => U_mem_nonempty X ((fixedNbhd_subsystem a).sub hX)

namespace sumComb

theorem eq (a b : ApproximableMap U U) :
    sumComb a b = (cond U).comp
      ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
          (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                  (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
        jPlus) := rfl

theorem toElementMap_mem (a b : ApproximableMap U U) (x : U.Element) {Z : Set ℚ} :
    ((sumComb a b).toElementMap x).mem Z ↔
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.zero ∧
        (iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.one ∧
        (iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      Z = U.master := by
  rw [eq]
  simp only [toElementMap_comp, toElementMap_paired]
  rw [cond_toElementMap_mem]

theorem toElementMap_of_left {a b : ApproximableMap U U} {x : U.Element}
    (hL : ∃ X, U.mem X ∧ (jPlus.toElementMap x).mem (inj₀ X)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have hz : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := which_mem_zero.mpr hL
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one :=
    fun h => not_sum_reaches_both hL (which_mem_one.mp h)
  apply Element.ext
  intro Z
  rw [toElementMap_mem]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | rfl)
    · exact h
    · exact absurd h1 hno
    · exact Element.master_mem _
  · intro h
    exact Or.inl ⟨hz, h⟩

theorem toElementMap_of_neither {a b : ApproximableMap U U} {x : U.Element}
    (hN : ∀ W, (jPlus.toElementMap x).mem W → W = (sum U U U_mem_nonempty U_mem_nonempty).master) :
    (sumComb a b).toElementMap x = U.bot := by
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := by
    rw [which_mem_zero]
    rintro ⟨X, _, hX⟩
    exact inj₀_ne_sumMaster (hN _ hX)
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := by
    rw [which_mem_one]
    rintro ⟨Y, _, hY⟩
    exact inj₁_ne_sumMaster (hN _ hY)
  apply Element.ext
  intro Z
  rw [toElementMap_mem, mem_bot]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
    · exact absurd h hnz
    · exact absurd h hno
    · exact h
  · intro h
    exact Or.inr (Or.inr h)

theorem toElementMap_of_right {a b : ApproximableMap U U} {x : U.Element}
    (hR : ∃ Y, U.mem Y ∧ (jPlus.toElementMap x).mem (inj₁ Y)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have ho : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := which_mem_one.mpr hR
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero :=
    fun h => not_sum_reaches_both (which_mem_zero.mp h) hR
  apply Element.ext
  intro Z
  rw [toElementMap_mem]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h⟩ | rfl)
    · exact absurd h1 hnz
    · exact h
    · exact Element.master_mem _
  · intro h
    exact Or.inr (Or.inl ⟨ho, h⟩)

theorem isRetraction {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (sumComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_of_left hL]
    set v := a.toElementMap (outMap₀.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))
        = inMap₀.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hLy : ∃ X, U.mem X ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))).mem (inj₀ X) := by
      rw [hjy]; exact inMap₀_toElementMap_reaches_left v
    rw [toElementMap_of_left hLy, hjy,
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀ v, toElementMap_idem_of_isRetraction ha]
  · rw [toElementMap_of_right hR]
    set v := b.toElementMap (outMap₁.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))
        = inMap₁.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hRy : ∃ Y, U.mem Y ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))).mem (inj₁ Y) := by
      rw [hjy]; exact inMap₁_toElementMap_reaches_right v
    rw [toElementMap_of_right hRy, hjy,
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁ v, toElementMap_idem_of_isRetraction hb]
  · rw [toElementMap_of_neither hN]
    apply toElementMap_of_neither
    intro W hW
    rw [jPlus_bot_eq_bot, mem_bot] at hW
    exact hW

theorem le_idMap {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    sumComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_of_left hL
      _ ≤ iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₀.toElementMap_mono (toElementMap_le_self_of_le_idMap ha _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₀_outMap₀_eq_of_left hL]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_of_right hR
      _ ≤ iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₁.toElementMap_mono (toElementMap_le_self_of_le_idMap hb _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₁_outMap₁_eq_of_right hR]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · rw [toElementMap_of_neither hN]
    exact U.bot_le x

theorem isProjection {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (sumComb a b) :=
  ⟨isRetraction ha.1 hb.1, le_idMap ha.2 hb.2⟩

noncomputable def I (a b : ApproximableMap U U) :
    ApproximableMap (sum (fixedNbhd a) (fixedNbhd b)
      (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) U :=
  iPlus.comp (sumMap (h₀' := U_mem_nonempty) (h₁' := U_mem_nonempty)
    (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

noncomputable def J (a b : ApproximableMap U U) :
    ApproximableMap U (sum (fixedNbhd a) (fixedNbhd b)
      (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) :=
  (sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)
    (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jPlus

end sumComb

end DomainTheory.NeighbourhoodSystems
