module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.plus7Body
public import DomainTheory.DataTypesAsLattices.Functionality.PlotkinHelpers
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.ContinuityHelpers
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Retracts.typed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def plus7 (a0 a1 a2 a3 a4 a5 a6 : Pomega) : Pomega :=
  graph (plus7Body a0 a1 a2 a3 a4 a5 a6)

namespace plus7

theorem map_isScottContinuous (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    IsScottContinuous (plus7Body a0 a1 a2 a3 a4 a5 a6) := by
  have htag (i : ℕ) (a : Pomega) :
      IsScottContinuous (fun u => tagInj i (funOf a (funOf u (ofNat 1)))) :=
    theorem_1_3 (tagInj.isScottContinuous i)
      (theorem_1_3 (funOf.isScottContinuous a)
        (funOf.isScottContinuous_left (ofNat 1)))
  have hz : IsScottContinuous (fun u => funOf u (ofNat 0)) :=
    funOf.isScottContinuous_left (ofNat 0)
  have hpred : ∀ k, IsScottContinuous
      (fun u => predSet^[k] (funOf u (ofNat 0))) := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      have h := theorem_1_3 (f := predSet)
        (g := fun u => predSet^[k] (funOf u (ofNat 0)))
        predSet.isScottContinuous ih
      convert h using 1
      funext u
      exact Function.iterate_succ_apply' predSet k (funOf u (ofNat 0))
  refine ContinuityHelpers.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    hz (htag 0 a0)
    (ContinuityHelpers.nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (hpred 1) (htag 1 a1)
      (ContinuityHelpers.nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (hpred 2) (htag 2 a2)
        (ContinuityHelpers.nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (hpred 3) (htag 3 a3)
          (ContinuityHelpers.nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (hpred 4) (htag 4 a4)
            (ContinuityHelpers.nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (hpred 5) (htag 5 a5)
              (ContinuityHelpers.nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (hpred 6) (htag 6 a6)
                (const_isScottContinuous topElem)))))))

theorem app (a0 a1 a2 a3 a4 a5 a6 u : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u =
      plus7Body a0 a1 a2 a3 a4 a5 a6 u :=
  beta (map_isScottContinuous a0 a1 a2 a3 a4 a5 a6) u

theorem bot (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) botElem = botElem := by
  rw [app, plus7Body, funOf.bot, dcondSet.bot]

theorem top (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) topElem = topElem := by
  rw [app, plus7Body, funOf.top, dcondSet.top]

theorem tag0 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_zero]

theorem tag1 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, predSet.ofNat_succ,
    dcondSet.ofNat_one, dcondSet.ofNat_zero]

theorem tag2 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet.ofNat_succ, dcondSet.ofNat_one,
    dcondSet.ofNat_zero]

theorem tag3 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag4 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 1),
    dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag5 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 2),
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 1),
    dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag6 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
  rw [app, plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 3),
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 2),
    dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 5) (i := 1),
    dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem comp_isScottContinuous
    {f0 f1 f2 f3 f4 f5 f6 : Pomega → Pomega}
    (h0 : IsScottContinuous f0) (h1 : IsScottContinuous f1)
    (h2 : IsScottContinuous f2) (h3 : IsScottContinuous f3)
    (h4 : IsScottContinuous f4) (h5 : IsScottContinuous f5)
    (h6 : IsScottContinuous f6) :
    IsScottContinuous (fun z =>
      plus7 (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z)) :=
  graph_const_isScottContinuous
    (fun z u => plus7Body (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z) u)
    (fun u => by
      have htag (i : ℕ) {f : Pomega → Pomega} (hf : IsScottContinuous f) :
          IsScottContinuous (fun z =>
            tagInj i (funOf (f z) (funOf u (ofNat 1)))) :=
        theorem_1_3 (f := tagInj i)
          (g := fun z => funOf (f z) (funOf u (ofNat 1)))
          (tagInj.isScottContinuous i)
          (theorem_1_3 (f := fun w => funOf w (funOf u (ofNat 1))) (g := f)
            (funOf.isScottContinuous_left (funOf u (ofNat 1))) hf)
      exact ContinuityHelpers.nary
        (fun y t => dcondSet.isScottContinuous_left y t)
        (fun x t => dcondSet.isScottContinuous_mid x t)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (const_isScottContinuous (funOf u (ofNat 0))) (htag 0 h0)
        (ContinuityHelpers.nary
          (fun y t => dcondSet.isScottContinuous_left y t)
          (fun x t => dcondSet.isScottContinuous_mid x t)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet (funOf u (ofNat 0)))) (htag 1 h1)
          (ContinuityHelpers.nary
            (fun y t => dcondSet.isScottContinuous_left y t)
            (fun x t => dcondSet.isScottContinuous_mid x t)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet (funOf u (ofNat 0)))))
            (htag 2 h2)
            (ContinuityHelpers.nary
              (fun y t => dcondSet.isScottContinuous_left y t)
              (fun x t => dcondSet.isScottContinuous_mid x t)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[3] (funOf u (ofNat 0))))
              (htag 3 h3)
              (ContinuityHelpers.nary
                (fun y t => dcondSet.isScottContinuous_left y t)
                (fun x t => dcondSet.isScottContinuous_mid x t)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[4] (funOf u (ofNat 0))))
                (htag 4 h4)
                (ContinuityHelpers.nary
                  (fun y t => dcondSet.isScottContinuous_left y t)
                  (fun x t => dcondSet.isScottContinuous_mid x t)
                  (fun x y => dcondSet.isScottContinuous_right x y)
                  (const_isScottContinuous (predSet^[5] (funOf u (ofNat 0))))
                  (htag 5 h5)
                  (ContinuityHelpers.nary
                    (fun y t => dcondSet.isScottContinuous_left y t)
                    (fun x t => dcondSet.isScottContinuous_mid x t)
                    (fun x y => dcondSet.isScottContinuous_right x y)
                    (const_isScottContinuous (predSet^[6] (funOf u (ofNat 0))))
                    (htag 6 h6) (const_isScottContinuous topElem))))))))

theorem isRetract {a0 a1 a2 a3 a4 a5 a6 : Pomega}
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
  rw [app, app]
  have hbody0 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_zero]
  have hbody1 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, predSet.ofNat_succ,
      dcondSet.ofNat_one, dcondSet.ofNat_zero]
  have hbody2 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, predSet.ofNat_succ,
      dcondSet.ofNat_succ, predSet.ofNat_succ, dcondSet.ofNat_one,
      dcondSet.ofNat_zero]
  have hbody3 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
      predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
      dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]
  have hbody4 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
      predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 1),
      dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]
  have hbody5 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
      predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 2),
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 1),
      dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]
  have hbody6 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
    rw [plus7Body, tagInj.zero, tagInj.one, dcondSet.ofNat_succ,
      predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 3),
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 2),
      dcondSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 5) (i := 1),
      dcondSet.ofNat_one, PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]
  have hbodyTop : plus7Body a0 a1 a2 a3 a4 a5 a6 topElem = topElem := by
    rw [plus7Body, funOf.top, dcondSet.top]
  have hbodyBot : plus7Body a0 a1 a2 a3 a4 a5 a6 botElem = botElem := by
    rw [plus7Body, funOf.bot, dcondSet.bot]
  rcases dcondSet.cases (funOf u (ofNat 0)) with hz | hz | hz | hz
  · have hL : plus7Body a0 a1 a2 a3 a4 a5 a6 u =
        tagInj 0 (funOf a0 (funOf u (ofNat 1))) := by
      rw [plus7Body, dcondSet.of_zero_not_pos hz.1 hz.2]
    rw [hL, hbody0, retract_app h0]
  · rw [plus7Body, dcondSet.of_pos_not_zero hz.1 hz.2]
    rcases dcondSet.cases (predSet (funOf u (ofNat 0))) with hz1 | hz1 | hz1 | hz1
    · rw [dcondSet.of_zero_not_pos hz1.1 hz1.2, hbody1, retract_app h1]
    · rw [dcondSet.of_pos_not_zero hz1.1 hz1.2]
      rcases dcondSet.cases (predSet (predSet (funOf u (ofNat 0)))) with
        hz2 | hz2 | hz2 | hz2
      · rw [dcondSet.of_zero_not_pos hz2.1 hz2.2, hbody2, retract_app h2]
      · rw [dcondSet.of_pos_not_zero hz2.1 hz2.2]
        rcases dcondSet.cases (predSet^[3] (funOf u (ofNat 0))) with
          hz3 | hz3 | hz3 | hz3
        · rw [dcondSet.of_zero_not_pos hz3.1 hz3.2, hbody3, retract_app h3]
        · rw [dcondSet.of_pos_not_zero hz3.1 hz3.2]
          rcases dcondSet.cases (predSet^[4] (funOf u (ofNat 0))) with
            hz4 | hz4 | hz4 | hz4
          · rw [dcondSet.of_zero_not_pos hz4.1 hz4.2, hbody4, retract_app h4]
          · rw [dcondSet.of_pos_not_zero hz4.1 hz4.2]
            rcases dcondSet.cases (predSet^[5] (funOf u (ofNat 0))) with
              hz5 | hz5 | hz5 | hz5
            · rw [dcondSet.of_zero_not_pos hz5.1 hz5.2, hbody5, retract_app h5]
            · rw [dcondSet.of_pos_not_zero hz5.1 hz5.2]
              rcases dcondSet.cases (predSet^[6] (funOf u (ofNat 0))) with
                hz6 | hz6 | hz6 | hz6
              · rw [dcondSet.of_zero_not_pos hz6.1 hz6.2, hbody6, retract_app h6]
              · rw [dcondSet.of_pos_not_zero hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet.of_mixed hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet.of_empty hz6.1 hz6.2, hbodyBot]
            · rw [dcondSet.of_mixed hz5.1 hz5.2, hbodyTop]
            · rw [dcondSet.of_empty hz5.1 hz5.2, hbodyBot]
          · rw [dcondSet.of_mixed hz4.1 hz4.2, hbodyTop]
          · rw [dcondSet.of_empty hz4.1 hz4.2, hbodyBot]
        · rw [dcondSet.of_mixed hz3.1 hz3.2, hbodyTop]
        · rw [dcondSet.of_empty hz3.1 hz3.2, hbodyBot]
      · rw [dcondSet.of_mixed hz2.1 hz2.2, hbodyTop]
      · rw [dcondSet.of_empty hz2.1 hz2.2, hbodyBot]
    · rw [dcondSet.of_mixed hz1.1 hz1.2, hbodyTop]
    · rw [dcondSet.of_empty hz1.1 hz1.2, hbodyBot]
  · rw [plus7Body, dcondSet.of_mixed hz.1 hz.2, hbodyTop]
  · rw [plus7Body, dcondSet.of_empty hz.1 hz.2, hbodyBot]

theorem typed_inl0 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a0) :
    typed (tagInj 0 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag0, ← hx]

theorem typed_inl1 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a1) :
    typed (tagInj 1 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag1, ← hx]

theorem typed_inl2 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a2) :
    typed (tagInj 2 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag2, ← hx]

theorem typed_inl3 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a3) :
    typed (tagInj 3 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag3, ← hx]

theorem typed_inl4 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a4) :
    typed (tagInj 4 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag4, ← hx]

theorem typed_inl5 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a5) :
    typed (tagInj 5 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag5, ← hx]

theorem typed_inl6 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a6) :
    typed (tagInj 6 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, tag6, ← hx]

end plus7

end DomainTheory.DataTypesAsLattices
