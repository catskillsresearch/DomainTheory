module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sumMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.expMap

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Exercise326
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem isProjection_combinators {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) :
    IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b) :=
  ⟨sumComb.isProjection ha hb, prodComb.isProjection ha hb, arrowComb.isProjection ha hb⟩

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

theorem inj_comp_proj_eq_self {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

theorem toElementMap_bot_eq_bot_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) : i.toElementMap D.bot = E.bot := by
  apply le_antisymm
  · calc i.toElementMap D.bot ≤ i.toElementMap (j.toElementMap E.bot) :=
          i.toElementMap_mono (D.bot_le _)
      _ ≤ E.bot := toElementMap_le_of_comp_le_idMap hij E.bot
  · exact E.bot_le _

theorem isFinitary_of_projectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    IsFinitary g :=
  ⟨α, D, ⟨(elementIsoOfProjectionPair i j hji hg).symm⟩⟩

namespace prodComb

theorem I_comp_J (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (prodComb.I a b).comp (prodComb.J a b) = prodComb a b := by
  unfold I J
  rw [comp_assoc, ← comp_assoc (prodMap _ _) (prodMap _ _) jTimes, ← prodMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc, prodComb.eq, comp_assoc]

noncomputable def elementIso (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (prodComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (prodComb.I a b) (prodComb.J a b) (prodComb.J_comp_I a b)
    (prodComb.I_comp_J a b ha hb).symm

theorem finitary (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (prodComb a b) :=
  isFinitary_of_projectionPair (prodComb.I a b) (prodComb.J a b) (prodComb.J_comp_I a b)
    (prodComb.I_comp_J a b ha hb).symm

theorem finitaryProjection (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (prodComb a b) :=
  ⟨⟨prodComb.isProjection ha.out.1 hb.out.1, prodComb.finitary a b ha hb⟩⟩

end prodComb

namespace arrowComb

theorem I_comp_J (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (arrowComb.I a b).comp (arrowComb.J a b) = arrowComb a b := by
  unfold I J
  rw [comp_assoc, ← comp_assoc (expMap _ _) (expMap _ _) jArrow, ← expMap.comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, expMap.eq_lamComb, ← comp_assoc,
    arrowComb.eq, comp_assoc]

noncomputable def elementIso (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (arrowComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (arrowComb.I a b) (arrowComb.J a b) (arrowComb.J_comp_I a b)
    (arrowComb.I_comp_J a b ha hb).symm

theorem finitary (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (arrowComb.I a b) (arrowComb.J a b) (arrowComb.J_comp_I a b)
    (arrowComb.I_comp_J a b ha hb).symm

theorem finitaryProjection (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (arrowComb a b) :=
  ⟨⟨arrowComb.isProjection ha.out.1 hb.out.1, arrowComb.finitary a b ha hb⟩⟩

end arrowComb

namespace sumComb

theorem eq_iPlus_sumMap_jPlus (a b : ApproximableMap U U) :
    sumComb a b = iPlus.comp
      ((sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty) (h₀' := U_mem_nonempty)
          (h₁' := U_mem_nonempty) a b).comp jPlus) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [sumComb.toElementMap_of_left hL, sumMap.toElementMap_of_left hL]
  · rw [sumComb.toElementMap_of_right hR, sumMap.toElementMap_of_right hR]
  · rw [sumComb.toElementMap_of_neither hN, sumMap.reaches_neither_iff_eq_bot.mp hN, sumMap.bot,
      toElementMap_bot_eq_bot_of_comp_le_idMap iPlus_comp_jPlus_le]

theorem I_comp_J (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (sumComb.I a b).comp (sumComb.J a b) = sumComb a b := by
  unfold I J
  rw [comp_assoc, ← comp_assoc (sumMap _ _) (sumMap _ _) jPlus, ← sumMap.comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc,
    eq_iPlus_sumMap_jPlus, comp_assoc]

theorem J_comp_I (a b : ApproximableMap U U) :
    (sumComb.J a b).comp (sumComb.I a b) =
      idMap (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
        (fixedNbhd_mem_nonempty b)) := by
  unfold J I
  rw [comp_assoc, ← comp_assoc jPlus iPlus (sumMap _ _), jPlus_comp_iPlus, idMap_comp,
    ← sumMap.comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    sumMap.id]

noncomputable def elementIso (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)).Element
      ≃o {y : U.Element // (sumComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (sumComb.I a b) (sumComb.J a b) (sumComb.J_comp_I a b)
    (sumComb.I_comp_J a b ha hb).symm

theorem finitary (a b : ApproximableMap U U) (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    IsFinitary (sumComb a b) :=
  isFinitary_of_projectionPair (sumComb.I a b) (sumComb.J a b) (sumComb.J_comp_I a b)
    (sumComb.I_comp_J a b ha hb).symm

theorem finitaryProjection (a b : ApproximableMap U U)
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) :=
  ⟨⟨sumComb.isProjection ha.out.1 hb.out.1, sumComb.finitary a b ha hb⟩⟩

end sumComb

theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) :=
  ⟨sumComb.finitaryProjection a b ha hb, prodComb.finitaryProjection a b ha hb,
    arrowComb.finitaryProjection a b ha hb⟩

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
  ⟨sumComb.finitaryProjection a b ha hb, prodComb.finitaryProjection a b ha hb,
    arrowComb.finitaryProjection a b ha hb, ⟨sumComb.elementIso a b ha hb⟩,
    ⟨prodComb.elementIso a b ha hb⟩, ⟨arrowComb.elementIso a b ha hb⟩⟩

end DomainTheory.NeighbourhoodSystems
