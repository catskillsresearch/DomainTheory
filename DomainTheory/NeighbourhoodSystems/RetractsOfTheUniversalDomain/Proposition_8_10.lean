module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap Exercise326
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/- concordance: source L5040 PROPOSITION 8.10 constructs preserve projections -/
/-- **Proposition 8.10 (Scott 1981, PRG-19), `→`-case.** `a, b` projections `⟹` `a → b` a
projection. -/
theorem isProjection_arrowComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (arrowComb a b) :=
  ⟨isRetraction_arrowComb ha.1 hb.1, le_idMap_arrowComb ha.2 hb.2⟩

/-- **`j₊` sends `𝒰`'s bottom to `𝒰+𝒰`'s bottom.** General fact: if `j ∘ i = I_D`, then `j(E.bot)`
is a global lower bound of `|D|` (via `D.bot ≤ i(v)` monotone through `j`, landing on
`j(i(D.bot)) = D.bot` for `v := D.bot`), hence equals `D.bot` by antisymmetry with `bot_le`. -/
theorem toElementMap_bot_eq_bot_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) : j.toElementMap E.bot = D.bot := by
  apply le_antisymm
  · have h2 := j.toElementMap_mono (E.bot_le (i.toElementMap D.bot))
    rwa [toElementMap_of_comp_eq_idMap hji] at h2
  · exact D.bot_le _

theorem jPlus_bot_eq_bot :
    jPlus.toElementMap U.bot = (sum U U U_mem_nonempty U_mem_nonempty).bot :=
  toElementMap_bot_eq_bot_of_comp_eq_idMap jPlus_comp_iPlus

theorem toElementMap_prodComb (a b : ApproximableMap U U) (x : U.Element) :
    (prodComb a b).toElementMap x =
      iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd)) := by
  rw [prodComb_eq]
  simp only [toElementMap_comp, toElementMap_prodMap]

/-- **Proposition 8.10, `×`-case, retraction half.** -/
theorem isRetraction_prodComb {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (prodComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_prodComb a b ((prodComb a b).toElementMap x),
    toElementMap_prodComb a b x, toElementMap_of_comp_eq_idMap jTimes_comp_iTimes, fst_pair,
    snd_pair, toElementMap_idem_of_isRetraction ha, toElementMap_idem_of_isRetraction hb]

/-- **Proposition 8.10, `×`-case, projection half.** -/
theorem le_idMap_prodComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    prodComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_prodComb, toElementMap_idMap]
  have hpair : pair (a.toElementMap (jTimes.toElementMap x).fst)
      (b.toElementMap (jTimes.toElementMap x).snd)
      ≤ pair (jTimes.toElementMap x).fst (jTimes.toElementMap x).snd :=
    pair_le_pair_iff.mpr
      ⟨toElementMap_le_self_of_le_idMap ha _, toElementMap_le_self_of_le_idMap hb _⟩
  rw [pair_fst_snd] at hpair
  calc iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd))
      ≤ iTimes.toElementMap (jTimes.toElementMap x) := iTimes.toElementMap_mono hpair
    _ ≤ x := toElementMap_le_of_comp_le_idMap iTimes_comp_jTimes_le x

/-- **Proposition 8.10 (Scott 1981, PRG-19), `×`-case.** `a, b` projections `⟹` `a × b` a
projection. -/
theorem isProjection_prodComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (prodComb a b) :=
  ⟨isRetraction_prodComb ha.1 hb.1, le_idMap_prodComb ha.2 hb.2⟩

/-- **Elementwise unfolding of `sumComb`.** Chains `sumComb_eq`, `toElementMap_comp`, and
`toElementMap_paired`, landing exactly on `cond_toElementMap_mem`'s pattern. -/
theorem toElementMap_sumComb_mem (a b : ApproximableMap U U) (x : U.Element) {Z : Set ℚ} :
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
  rw [sumComb_eq]
  simp only [toElementMap_comp, toElementMap_paired]
  rw [cond_toElementMap_mem]

/-- **On a "left" point** (`jPlus x` reaches the left copy), `sumComb a b` evaluates to Scott's
literal `i₊∘in₀∘a∘out₀` formula. -/
theorem toElementMap_sumComb_of_left {a b : ApproximableMap U U} {x : U.Element}
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
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | rfl)
    · exact h
    · exact absurd h1 hno
    · exact Element.master_mem _
  · intro h
    exact Or.inl ⟨hz, h⟩

/-- **On a point reaching neither copy** (in particular, `𝒰`'s own `⊥`, via `jPlus_bot_eq_bot`),
`sumComb a b` sends it to `𝒰`'s `⊥`. -/
theorem toElementMap_sumComb_of_neither {a b : ApproximableMap U U} {x : U.Element}
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
  rw [toElementMap_sumComb_mem, mem_bot]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
    · exact absurd h hnz
    · exact absurd h hno
    · exact h
  · intro h
    exact Or.inr (Or.inr h)

/-- **On a "right" point**, symmetric to `toElementMap_sumComb_of_left`. -/
theorem toElementMap_sumComb_of_right {a b : ApproximableMap U U} {x : U.Element}
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
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h⟩ | rfl)
    · exact absurd h1 hnz
    · exact h
    · exact Element.master_mem _
  · intro h
    exact Or.inr (Or.inl ⟨ho, h⟩)

/-- **Proposition 8.10, `+`-case, retraction half.** -/
theorem isRetraction_sumComb {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (sumComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL]
    set v := a.toElementMap (outMap₀.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))
        = inMap₀.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hLy : ∃ X, U.mem X ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))).mem (inj₀ X) := by
      rw [hjy]; exact inMap₀_toElementMap_reaches_left v
    rw [toElementMap_sumComb_of_left hLy, hjy,
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀ v, toElementMap_idem_of_isRetraction ha]
  · rw [toElementMap_sumComb_of_right hR]
    set v := b.toElementMap (outMap₁.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))
        = inMap₁.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hRy : ∃ Y, U.mem Y ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))).mem (inj₁ Y) := by
      rw [hjy]; exact inMap₁_toElementMap_reaches_right v
    rw [toElementMap_sumComb_of_right hRy, hjy,
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁ v, toElementMap_idem_of_isRetraction hb]
  · rw [toElementMap_sumComb_of_neither hN]
    apply toElementMap_sumComb_of_neither
    intro W hW
    rw [jPlus_bot_eq_bot, mem_bot] at hW
    exact hW

/-- **Proposition 8.10, `+`-case, projection half.** -/
theorem le_idMap_sumComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    sumComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_left hL
      _ ≤ iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₀.toElementMap_mono (toElementMap_le_self_of_le_idMap ha _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₀_outMap₀_eq_of_left hL]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_right hR
      _ ≤ iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₁.toElementMap_mono (toElementMap_le_self_of_le_idMap hb _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₁_outMap₁_eq_of_right hR]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · rw [toElementMap_sumComb_of_neither hN]
    exact U.bot_le x

/-- **Proposition 8.10 (Scott 1981, PRG-19), `+`-case.** `a, b` projections `⟹` `a + b` a
projection. -/
theorem isProjection_sumComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (sumComb a b) :=
  ⟨isRetraction_sumComb ha.1 hb.1, le_idMap_sumComb ha.2 hb.2⟩

/-- **Proposition 8.10 (Scott 1981, PRG-19), first half.** If `a, b : 𝒰 → 𝒰` are projections,
then so are `a+b`, `a×b`, and `a→b`. -/
theorem isProjection_combinators {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) :
    IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b) :=
  ⟨isProjection_sumComb ha hb, isProjection_prodComb ha hb, isProjection_arrowComb ha hb⟩

end

set_option linter.unusedVariables false

theorem theorem_810 : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
  (∀
    {a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @LE.le
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          (DomainTheory.NeighbourhoodSystems.sumComb a b)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
  (∀
    {a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @LE.le
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          (DomainTheory.NeighbourhoodSystems.sumComb a b)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)))
      (@And.intro
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
        (@And.intro
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b))
          (@And.intro
            (And
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b))
            (@And.intro
              (And
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b))
              (@And.intro
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                (@And.intro
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b))
                  (@And.intro
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b))
                    (@And.intro
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
                      @DomainTheory.NeighbourhoodSystems.isProjection_arrowComb
                      @DomainTheory.NeighbourhoodSystems.isProjection_combinators)
                    @DomainTheory.NeighbourhoodSystems.isProjection_prodComb)
                  @DomainTheory.NeighbourhoodSystems.isProjection_sumComb)
                @DomainTheory.NeighbourhoodSystems.isRetraction_arrowComb)
              @DomainTheory.NeighbourhoodSystems.isRetraction_lamComb)
            @DomainTheory.NeighbourhoodSystems.isRetraction_prodComb)
          @DomainTheory.NeighbourhoodSystems.isRetraction_sumComb)
        @DomainTheory.NeighbourhoodSystems.le_idMap_arrowComb)
      @DomainTheory.NeighbourhoodSystems.le_idMap_lamComb)
    @DomainTheory.NeighbourhoodSystems.le_idMap_prodComb)
  @DomainTheory.NeighbourhoodSystems.le_idMap_sumComb

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

/-- **`I_× : D_a × D_b → 𝒰`**, built by transporting `i_×` (Definition 8.9) through the functorial
action of `×` (Exercise 3.19's `prodMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def IProdComb : ApproximableMap (prod (fixedNbhd a) (fixedNbhd b)) U :=
  iTimes.comp (prodMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

/-- **`J_× : 𝒰 → D_a × D_b`**, symmetric to `IProdComb`, via the projections `j_a`, `j_b`. -/
noncomputable def JProdComb : ApproximableMap U (prod (fixedNbhd a) (fixedNbhd b)) :=
  (prodMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jTimes

theorem JProdComb_comp_IProdComb :
    (JProdComb a b).comp (IProdComb a b) = idMap (prod (fixedNbhd a) (fixedNbhd b)) := by
  unfold JProdComb IProdComb
  rw [comp_assoc, ← comp_assoc jTimes iTimes (prodMap _ _), jTimes_comp_iTimes, idMap_comp,
    ← prodMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    prodMap_id]

end ProdCase

end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Generalized Proposition 8.2 `elementIso`.** Given an approximable projection pair
`i : D → E`, `j : E → D` with `j ∘ i = I_D` (no requirement `i ∘ j ≤ I_E`, and `D`, `E` need not
share a token type — unlike `Subsystem.elementIso`, which requires a literal `D ◁ E`), and
`g : E → E` with `g = i ∘ j`, then `D.Element ≃o Fix(g)`. The proof is verbatim
`Subsystem.elementIso`'s, generalized. -/
def elementIsoOfProjectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    D.Element ≃o {y : E.Element // g.toElementMap y = y} where
  toFun x := ⟨i.toElementMap x, by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    rw [hg, toElementMap_comp, h1, hji, toElementMap_idMap]⟩
  invFun y := j.toElementMap y.1
  left_inv x := by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    show j.toElementMap (i.toElementMap x) = x
    rw [h1, hji, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : g.toElementMap y.1 = y.1 := y.2
    show i.toElementMap (j.toElementMap y.1) = y.1
    rw [← toElementMap_comp, ← hg]
    exact hfix
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := j.toElementMap_mono hle
      have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
        (toElementMap_comp j i x).symm
      have h2 : j.toElementMap (i.toElementMap x') = (j.comp i).toElementMap x' :=
        (toElementMap_comp j i x').symm
      rw [h1, h2, hji, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact i.toElementMap_mono hle
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {a b : ApproximableMap U U}

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **The Hom-functor's action on maps**, `f ↦ k∘f∘h`, transported to the function-space
neighbourhood systems via `curry`/`evalMap`/`prodMap`, exactly as `lamComb` (`Definition89.lean`)
does for the self-map case. -/
noncomputable def expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    ApproximableMap (funSpace V0 V1) (funSpace V0' V1') :=
  curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h)))

end ExpMap

section ArrowCase

variable (a b : ApproximableMap U U)

/-- **`I_→ : (D_a → D_b) → 𝒰`**, built by transporting `i_→` (Definition 8.9) through the
functorial action of `→` (`expMap`) on `j_a : 𝒰 → D_a` (contravariant slot) and
`i_b : D_b → 𝒰` (covariant slot). -/
noncomputable def IArrowComb : ApproximableMap (funSpace (fixedNbhd a) (fixedNbhd b)) U :=
  iArrow.comp (expMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).inj)

/-- **`J_→ : 𝒰 → (D_a → D_b)`**, symmetric to `IArrowComb`, via `i_a` (contravariant) and
`j_b` (covariant). -/
noncomputable def JArrowComb : ApproximableMap U (funSpace (fixedNbhd a) (fixedNbhd b)) :=
  (expMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).proj).comp jArrow

end ArrowCase

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

theorem expMap_eq (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    expMap h k = curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h))) := rfl

/-- `expMap` specializes to `lamComb` on self-maps of `𝒰`. -/
theorem expMap_eq_lamComb (a b : ApproximableMap U U) : expMap a b = lamComb a b := rfl

end ExpMap

/-- Every neighbourhood of `D_a := fixedNbhd a` is non-empty (inherited from `𝒰`). -/
theorem fixedNbhd_mem_nonempty (a : ApproximableMap U U) :
    ∀ X, (fixedNbhd a).mem X → X.Nonempty :=
  fun X hX => U_mem_nonempty X ((fixedNbhd_subsystem a).sub hX)

section SumCase

variable (a b : ApproximableMap U U)

/-- **`I_+ : D_a + D_b → 𝒰`**, built by transporting `i₊` (Definition 8.9) through the functorial
action of `+` (Exercise 3.19's `sumMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def ISumComb : ApproximableMap (sum (fixedNbhd a) (fixedNbhd b)
    (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) U :=
  iPlus.comp (sumMap (h₀' := U_mem_nonempty) (h₁' := U_mem_nonempty)
    (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

/-- **`J_+ : 𝒰 → D_a + D_b`**, symmetric to `ISumComb`, via the projections `j_a`, `j_b`. -/
noncomputable def JSumComb : ApproximableMap U (sum (fixedNbhd a) (fixedNbhd b)
    (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) :=
  (sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)
    (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jPlus

end SumCase

/-- **`i_a ∘ j_a = a`, for a finitary projection `a`.** Theorem 8.6's `sub_eq_self_of_isFinitaryProjection`,
restated via `retractionOfSubsystem`'s definition. -/
theorem inj_comp_proj_eq_self (ha : FinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

section ProdCase

variable (a b : ApproximableMap U U)

theorem IProdComb_comp_JProdComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (IProdComb a b).comp (JProdComb a b) = prodComb a b := by
  unfold IProdComb JProdComb
  rw [comp_assoc, ← comp_assoc (prodMap _ _) (prodMap _ _) jTimes, ← prodMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc, prodComb_eq, comp_assoc]

/-- **Proposition 8.10(b), `×`-case, the isomorphism `D_{a×b} ≅ D_a × D_b`.** -/
noncomputable def prodComb_elementIso (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (prodComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

end ProdCase

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

/-- A sum-element reaches "neither" copy iff it is the bottom element. -/
theorem reaches_neither_iff_eq_bot {y : (sum V0 V1 h0 h1).Element} :
    (∀ W, y.mem W → W = (sum V0 V1 h0 h1).master) ↔ y = (sum V0 V1 h0 h1).bot := by
  constructor
  · intro hN
    apply Element.ext
    intro W
    rw [mem_bot]
    exact ⟨hN W, fun h => h ▸ y.master_mem⟩
  · rintro rfl W hW
    rw [mem_bot] at hW
    exact hW

/-- `sumMap` sends the bottom element to the bottom element. -/
theorem sumMap_bot (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1') :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        (sum V0 V1 h0 h1).bot = (sum V0' V1' h0' h1').bot := by
  apply Element.ext
  intro Z
  rw [mem_bot]
  constructor
  · rintro ⟨W, hW, _, hZmem, hd⟩
    rw [mem_bot] at hW
    subst hW
    rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨Y, Y', hWY, -, -⟩
    · rfl
    · have hWX' : sumMaster V0 V1 = inj₀ X := hWX
      exact absurd (hWX' ▸ none_mem_sumMaster) none_mem_inj₀
    · have hWY' : sumMaster V0 V1 = inj₁ Y := hWY
      exact absurd (hWY' ▸ none_mem_sumMaster) none_mem_inj₁
  · rintro rfl
    exact ⟨sumMaster V0 V1, (sum V0 V1 h0 h1).mem_bot.mpr rfl, (sum V0 V1 h0 h1).master_mem,
      (sum V0' V1' h0' h1').master_mem, Or.inl rfl⟩

/-- If `y` reaches the left copy, `(sumMap f g)(y)` also reaches the left copy. -/
theorem sumMap_reaches_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    ∃ X', V0'.mem X' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₀ X') := by
  obtain ⟨X, hX, hXy⟩ := hL
  have hf : f.rel X V0'.master :=
    f.mono f.master_rel (V0.sub_master hX) subset_rfl hX V0'.master_mem
  exact ⟨V0'.master, V0'.master_mem, inj₀ X, hXy,
    Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨V0'.master, V0'.master_mem, rfl⟩),
    Or.inr (Or.inl ⟨X, V0'.master, rfl, rfl, hf⟩)⟩

/-- If `y` reaches the right copy, `(sumMap f g)(y)` also reaches the right copy. -/
theorem sumMap_reaches_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    ∃ Y', V1'.mem Y' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₁ Y') := by
  obtain ⟨Y, hY, hYy⟩ := hR
  have hg : g.rel Y V1'.master :=
    g.mono g.master_rel (V1.sub_master hY) subset_rfl hY V1'.master_mem
  exact ⟨V1'.master, V1'.master_mem, inj₁ Y, hYy,
    Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨V1'.master, V1'.master_mem, rfl⟩),
    Or.inr (Or.inr ⟨Y, V1'.master, rfl, rfl, hg⟩)⟩

end SumMapLemmas

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **`expMap h k`, transported through `funSpaceEquiv`, is exactly `f ↦ k∘f∘h`.** Verbatim
`toApproxMap_toElementMap_lamComb`'s proof (`Proposition810.lean`), generalized away from
self-maps. -/
theorem toApproxMap_toElementMap_expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (φ : (funSpace V0 V1).Element) :
    toApproxMap ((expMap h k).toElementMap φ) = k.comp ((toApproxMap φ).comp h) := by
  apply ext_of_toElementMap
  intro z
  rw [expMap_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

/-- **`expMap` preserves composition, contravariantly in `h`:
`expMap (h∘h') (k'∘k) = expMap h' k' ∘ expMap h k`.** -/
theorem expMap_comp (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (h' : ApproximableMap V0'' V0') (k' : ApproximableMap V1' V1'') :
    expMap (h.comp h') (k'.comp k) = (expMap h' k').comp (expMap h k) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0'' V1'').injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap, toElementMap_comp,
    toApproxMap_toElementMap_expMap, toApproxMap_toElementMap_expMap]
  simp only [comp_assoc]

end ExpMap

section ArrowCase

variable (a b : ApproximableMap U U)

theorem IArrowComb_comp_JArrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (IArrowComb a b).comp (JArrowComb a b) = arrowComb a b := by
  unfold IArrowComb JArrowComb
  rw [comp_assoc, ← comp_assoc (expMap _ _) (expMap _ _) jArrow, ← expMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, expMap_eq_lamComb, ← comp_assoc,
    arrowComb_eq, comp_assoc]

end ArrowCase

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **`expMap` preserves identities: `expMap I I = I`.** -/
theorem expMap_id : expMap (idMap V0) (idMap V1) = idMap (funSpace V0 V1) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0 V1).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_idMap,
    toApproxMap_toElementMap_expMap, comp_idMap, idMap_comp]

end ExpMap

section ArrowCase

variable (a b : ApproximableMap U U)

theorem JArrowComb_comp_IArrowComb :
    (JArrowComb a b).comp (IArrowComb a b) =
      idMap (funSpace (fixedNbhd a) (fixedNbhd b)) := by
  unfold JArrowComb IArrowComb
  rw [comp_assoc, ← comp_assoc jArrow iArrow (expMap _ _), jArrow_comp_iArrow, idMap_comp,
    ← expMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    expMap_id]

/-- **Proposition 8.10(b), `→`-case, the isomorphism `D_{a→b} ≅ (D_a → D_b)`.** -/
noncomputable def arrowComb_elementIso (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (arrowComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

end ArrowCase

end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- If `i ∘ j ≤ I_E`, then `i` sends `D`'s bottom to `E`'s bottom: `i(⊥_D) ≤ i(j(⊥_E)) ≤ ⊥_E`
(the first step by monotonicity, since `⊥_D ≤ j(⊥_E)`; the second is `toElementMap_le_of_comp_le_idMap`
at `x := ⊥_E`), and `⊥_E ≤ i(⊥_D)` always. -/
theorem toElementMap_bot_eq_bot_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) : i.toElementMap D.bot = E.bot := by
  apply le_antisymm
  · calc i.toElementMap D.bot ≤ i.toElementMap (j.toElementMap E.bot) :=
          i.toElementMap_mono (D.bot_le _)
      _ ≤ E.bot := toElementMap_le_of_comp_le_idMap hij E.bot
  · exact E.bot_le _
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {a b : ApproximableMap U U}

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

theorem toElementMap_sumMap_inMap₀ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (v : V0.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap (f.toElementMap v) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) with hz
  have hLz : ∃ X', V0'.mem X' ∧ z.mem (inj₀ X') :=
    sumMap_reaches_left (inMap₀_toElementMap_reaches_left v)
  rw [← inMap₀_outMap₀_eq_of_left hLz]
  congr 1
  have heq : (outMap₀ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₀ (h₀ := h0) (h₁ := h1))) = f :=
    outMap₀_comp_sumMap_comp_inMap₀ f g
  calc (outMap₀ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₀ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₀ (h₀ := h0) (h₁ := h1)))).toElementMap v := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = f.toElementMap v := by rw [heq]

theorem toElementMap_sumMap_inMap₁ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (w : V1.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap (g.toElementMap w) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) with hz
  have hRz : ∃ Y', V1'.mem Y' ∧ z.mem (inj₁ Y') :=
    sumMap_reaches_right (inMap₁_toElementMap_reaches_right w)
  rw [← inMap₁_outMap₁_eq_of_right hRz]
  congr 1
  have heq : (outMap₁ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₁ (h₀ := h0) (h₁ := h1))) = g :=
    outMap₁_comp_sumMap_comp_inMap₁ f g
  calc (outMap₁ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₁ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₁ (h₀ := h0) (h₁ := h1)))).toElementMap w := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = g.toElementMap w := by rw [heq]

theorem toElementMap_sumMap_of_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap
        (f.toElementMap ((outMap₀ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₀_outMap₀_eq_of_left hL]
  exact toElementMap_sumMap_inMap₀ f g _

theorem toElementMap_sumMap_of_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap
        (g.toElementMap ((outMap₁ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₁_outMap₁_eq_of_right hR]
  exact toElementMap_sumMap_inMap₁ f g _

end SumMapLemmas

section SumCase

variable (a b : ApproximableMap U U)

/-- **`sumComb a b = i₊ ∘ (a+b) ∘ j₊`, at the level of approximable maps**, where `a+b` on the
right is Exercise 3.19's `sumMap`. Proved by case-splitting on `sum_element_trichotomy` of
`jPlus.toElementMap x`, matching `sumMap`'s elementwise formulas
(`toElementMap_sumMap_of_left/right`, `sumMap_bot`) against `sumComb`'s own
(`toElementMap_sumComb_of_left/right/neither`, `Proposition810.lean`). The bottom case additionally
needs `iPlus.toElementMap (sum U U ..).bot = U.bot`, from `iPlus_comp_jPlus_le`. -/
theorem sumComb_eq_iPlus_sumMap_jPlus :
    sumComb a b = iPlus.comp
      ((sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty) (h₀' := U_mem_nonempty)
          (h₁' := U_mem_nonempty) a b).comp jPlus) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL, toElementMap_sumMap_of_left hL]
  · rw [toElementMap_sumComb_of_right hR, toElementMap_sumMap_of_right hR]
  · rw [toElementMap_sumComb_of_neither hN, reaches_neither_iff_eq_bot.mp hN, sumMap_bot,
      toElementMap_bot_eq_bot_of_comp_le_idMap iPlus_comp_jPlus_le]

end SumCase

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

/-- **`sumMap` preserves composition: `(f'∘f) + (g'∘g) = (f'+g') ∘ (f+g)`.** -/
theorem sumMap_comp (f' : ApproximableMap V0' V0'') (f : ApproximableMap V0 V0')
    (g' : ApproximableMap V1' V1'') (g : ApproximableMap V1 V1') :
    sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0'') (h₁' := h1'') (f'.comp f) (g'.comp g) =
      (sumMap (h₀ := h0') (h₁ := h1') (h₀' := h0'') (h₁' := h1'') f' g').comp
        (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_comp, toElementMap_sumMap_of_left hL,
      toElementMap_sumMap_of_left (inMap₀_toElementMap_reaches_left _),
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_comp, toElementMap_sumMap_of_right hR,
      toElementMap_sumMap_of_right (inMap₁_toElementMap_reaches_right _),
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot, sumMap_bot, sumMap_bot]

end SumMapLemmas

section SumCase

variable (a b : ApproximableMap U U)

theorem ISumComb_comp_JSumComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (ISumComb a b).comp (JSumComb a b) = sumComb a b := by
  unfold ISumComb JSumComb
  rw [comp_assoc, ← comp_assoc (sumMap _ _) (sumMap _ _) jPlus, ← sumMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc,
    sumComb_eq_iPlus_sumMap_jPlus, comp_assoc]

end SumCase

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}

variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}

variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

/-- **`sumMap` preserves identities: `id + id = id`.** -/
theorem sumMap_id : sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0) (h₁' := h1)
    (idMap V0) (idMap V1) = idMap (sum V0 V1 h0 h1) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_idMap, inMap₀_outMap₀_eq_of_left hL]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_idMap, inMap₁_outMap₁_eq_of_right hR]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot]

end SumMapLemmas

section SumCase

variable (a b : ApproximableMap U U)

theorem JSumComb_comp_ISumComb :
    (JSumComb a b).comp (ISumComb a b) =
      idMap (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
        (fixedNbhd_mem_nonempty b)) := by
  unfold JSumComb ISumComb
  rw [comp_assoc, ← comp_assoc jPlus iPlus (sumMap _ _), jPlus_comp_iPlus, idMap_comp,
    ← sumMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    sumMap_id]

/-- **Proposition 8.10(b), `+`-case, the isomorphism `D_{a+b} ≅ D_a + D_b`.** -/
noncomputable def sumComb_elementIso (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)).Element
      ≃o {y : U.Element // (sumComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

end SumCase

end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **`IsFinitary` from a concrete projection-pair witness.** -/
theorem isFinitary_of_projectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    IsFinitary g :=
  ⟨α, D, ⟨(elementIsoOfProjectionPair i j hji hg).symm⟩⟩
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {a b : ApproximableMap U U}

section ArrowCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `→`-case.** `a, b` finitary projections `⟹` `a → b` is finitary, with
witnessing domain `D_a → D_b`. -/
theorem finitary_arrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

/-- **Proposition 8.10(b), `→`-case, in full.** `a, b` finitary projections `⟹` `a → b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a → D_b`. -/
theorem finitaryProjection_arrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (arrowComb a b) :=
  ⟨⟨isProjection_arrowComb ha.out.1 hb.out.1, finitary_arrowComb a b ha hb⟩⟩

end ArrowCase

section ProdCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `×`-case.** `a, b` finitary projections `⟹` `a × b` is finitary, with
witnessing domain `D_a × D_b`. -/
theorem finitary_prodComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (prodComb a b) :=
  isFinitary_of_projectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

/-- **Proposition 8.10(b), `×`-case, in full.** `a, b` finitary projections `⟹` `a × b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a × D_b`. -/
theorem finitaryProjection_prodComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (prodComb a b) :=
  ⟨⟨isProjection_prodComb ha.out.1 hb.out.1, finitary_prodComb a b ha hb⟩⟩

end ProdCase

section SumCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `+`-case.** `a, b` finitary projections `⟹` `a + b` is finitary, with
witnessing domain `D_a + D_b`. -/
theorem finitary_sumComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (sumComb a b) :=
  isFinitary_of_projectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

/-- **Proposition 8.10(b), `+`-case, in full.** `a, b` finitary projections `⟹` `a + b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a + D_b`. -/
theorem finitaryProjection_sumComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) :=
  ⟨⟨isProjection_sumComb ha.out.1 hb.out.1, finitary_sumComb a b ha hb⟩⟩

end SumCase

/-- **Proposition 8.10(b) (Scott 1981, PRG-19), in full.** If `a, b : 𝒰 → 𝒰` are finitary
projections, then so are `a+b`, `a×b`, `a→b`, with `D_{a+b} ≅ D_a+D_b`, `D_{a×b} ≅ D_a×D_b`,
`D_{a→b} ≅ (D_a→D_b)`. -/
theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb⟩

end

open NeighborhoodSystem ApproximableMap

/-- **Proposition 8.10 (Scott 1981, PRG-19).** If `a, b : 𝒰 → 𝒰` are finitary projections, then
so are `a+b`, `a×b`, and `a→b`, and `D_{a+b} ≅ D_a + D_b`, `D_{a×b} ≅ D_a × D_b`,
`D_{a→b} ≅ (D_a → D_b)`, where `D_a = fixedNbhd a` and `D_b = fixedNbhd b`. -/
theorem proposition_8_10 {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) ∧
      Nonempty
        ((sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
            (fixedNbhd_mem_nonempty b)).Element ≃o
          {y : U.Element // (sumComb a b).toElementMap y = y}) ∧
      Nonempty
        ((prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (prodComb a b).toElementMap y = y}) ∧
      Nonempty
        ((funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (arrowComb a b).toElementMap y = y}) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb, ⟨sumComb_elementIso a b ha hb⟩,
    ⟨prodComb_elementIso a b ha hb⟩, ⟨arrowComb_elementIso a b ha hb⟩⟩

set_option linter.unusedVariables false

theorem theorem_810_b : And
  (And
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
  (∀
    (a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U),
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.sumComb a b)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
  (∀
    (a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U),
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.sumComb a b))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b))
    (@And.intro
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
      (@And.intro
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b))
        (@And.intro
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
          (@And.intro
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
            (@And.intro
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b))
              (@DomainTheory.NeighbourhoodSystems.proposition_8_10)
              DomainTheory.NeighbourhoodSystems.finitaryProjection_arrowComb)
            @DomainTheory.NeighbourhoodSystems.finitaryProjection_combinators)
          DomainTheory.NeighbourhoodSystems.finitaryProjection_prodComb)
        DomainTheory.NeighbourhoodSystems.finitaryProjection_sumComb)
      DomainTheory.NeighbourhoodSystems.finitary_arrowComb)
    DomainTheory.NeighbourhoodSystems.finitary_prodComb)
  DomainTheory.NeighbourhoodSystems.finitary_sumComb

end DomainTheory.NeighbourhoodSystems
