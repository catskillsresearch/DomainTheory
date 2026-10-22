
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_isRetract {a0 a1 a2 a3 a4 a5 a6 : Pomega}
    (h0 : Retract a0) (h1 : Retract a1) (h2 : Retract a2)
    (h3 : Retract a3) (h4 : Retract a4) (h5 : Retract a5)
    (h6 : Retract a6) :
    Retract (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  constructor
  change plus7 a0 a1 a2 a3 a4 a5 a6 =
    graph (fun u => funOf (plus7 a0 a1 a2 a3 a4 a5 a6)
      (funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u))
  apply graph_ext
  intro u
  rw [plus7_app, plus7_app]
  have hbody0 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_zero]
  have hbody1 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
      dcondSet_ofNat_one, dcondSet_ofNat_zero]
  have hbody2 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_ofNat_succ, dcondSet_ofNat_one,
      dcondSet_ofNat_zero]
  have hbody3 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody4 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody5 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody6 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 2),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 5) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbodyTop : plus7Body a0 a1 a2 a3 a4 a5 a6 topElem = topElem := by
    rw [plus7Body, funOf_top, dcondSet_top]
  have hbodyBot : plus7Body a0 a1 a2 a3 a4 a5 a6 botElem = botElem := by
    rw [plus7Body, funOf_bot, dcondSet_bot]
  rcases dcondSet_cases (funOf u (ofNat 0)) with hz | hz | hz | hz
  · have hL : plus7Body a0 a1 a2 a3 a4 a5 a6 u =
        tagInj 0 (funOf a0 (funOf u (ofNat 1))) := by
      rw [plus7Body, dcondSet_of_zero_not_pos hz.1 hz.2]
    rw [hL, hbody0, retract_app h0]
  · rw [plus7Body, dcondSet_of_pos_not_zero hz.1 hz.2]
    rcases dcondSet_cases (predSet (funOf u (ofNat 0))) with hz1 | hz1 | hz1 | hz1
    · rw [dcondSet_of_zero_not_pos hz1.1 hz1.2, hbody1, retract_app h1]
    · rw [dcondSet_of_pos_not_zero hz1.1 hz1.2]
      rcases dcondSet_cases (predSet (predSet (funOf u (ofNat 0)))) with
        hz2 | hz2 | hz2 | hz2
      · rw [dcondSet_of_zero_not_pos hz2.1 hz2.2, hbody2, retract_app h2]
      · rw [dcondSet_of_pos_not_zero hz2.1 hz2.2]
        rcases dcondSet_cases (predSet^[3] (funOf u (ofNat 0))) with
          hz3 | hz3 | hz3 | hz3
        · rw [dcondSet_of_zero_not_pos hz3.1 hz3.2, hbody3, retract_app h3]
        · rw [dcondSet_of_pos_not_zero hz3.1 hz3.2]
          rcases dcondSet_cases (predSet^[4] (funOf u (ofNat 0))) with
            hz4 | hz4 | hz4 | hz4
          · rw [dcondSet_of_zero_not_pos hz4.1 hz4.2, hbody4, retract_app h4]
          · rw [dcondSet_of_pos_not_zero hz4.1 hz4.2]
            rcases dcondSet_cases (predSet^[5] (funOf u (ofNat 0))) with
              hz5 | hz5 | hz5 | hz5
            · rw [dcondSet_of_zero_not_pos hz5.1 hz5.2, hbody5, retract_app h5]
            · rw [dcondSet_of_pos_not_zero hz5.1 hz5.2]
              rcases dcondSet_cases (predSet^[6] (funOf u (ofNat 0))) with
                hz6 | hz6 | hz6 | hz6
              · rw [dcondSet_of_zero_not_pos hz6.1 hz6.2, hbody6, retract_app h6]
              · rw [dcondSet_of_pos_not_zero hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet_of_mixed hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet_of_empty hz6.1 hz6.2, hbodyBot]
            · rw [dcondSet_of_mixed hz5.1 hz5.2, hbodyTop]
            · rw [dcondSet_of_empty hz5.1 hz5.2, hbodyBot]
          · rw [dcondSet_of_mixed hz4.1 hz4.2, hbodyTop]
          · rw [dcondSet_of_empty hz4.1 hz4.2, hbodyBot]
        · rw [dcondSet_of_mixed hz3.1 hz3.2, hbodyTop]
        · rw [dcondSet_of_empty hz3.1 hz3.2, hbodyBot]
      · rw [dcondSet_of_mixed hz2.1 hz2.2, hbodyTop]
      · rw [dcondSet_of_empty hz2.1 hz2.2, hbodyBot]
    · rw [dcondSet_of_mixed hz1.1 hz1.2, hbodyTop]
    · rw [dcondSet_of_empty hz1.1 hz1.2, hbodyBot]
  · rw [plus7Body, dcondSet_of_mixed hz.1 hz.2, hbodyTop]
  · rw [plus7Body, dcondSet_of_empty hz.1 hz.2, hbodyBot]

end DomainTheory.DataTypesAsLattices
