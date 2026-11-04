module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Enumeration.ContinuityHelpers
public import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Retracts.typed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

namespace plusR

theorem map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))) :=
  ContinuityHelpers.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (theorem_1_3 (PairSeq.isScottContinuous_right (ofNat 0))
      (theorem_1_3 (funOf.isScottContinuous a)
        (funOf.isScottContinuous_left (ofNat 1))))
    (theorem_1_3 (PairSeq.isScottContinuous_right (ofNat 1))
      (theorem_1_3 (funOf.isScottContinuous b)
        (funOf.isScottContinuous_left (ofNat 1))))

theorem right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => plusR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))
    (fun u =>
      theorem_1_3
        (f := fun y =>
          dcondSet (funOf u (ofNat 0))
            (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))) y)
        (g := fun b => pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))
        (dcondSet.isScottContinuous_right
          (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))))
        (theorem_1_3 (PairSeq.isScottContinuous_right (ofNat 1))
          (funOf.isScottContinuous_left (funOf u (ofNat 1)))))

theorem app (a b u : Pomega) :
    funOf (plusR a b) u =
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) :=
  beta (map_isScottContinuous a b) u

theorem bot (a b : Pomega) :
    funOf (plusR a b) botElem = botElem := by
  rw [app, funOf.bot, dcondSet.bot]

theorem top (a b : Pomega) :
    funOf (plusR a b) topElem = topElem := by
  rw [app, funOf.top, dcondSet.top]

theorem fst (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 0) =
      dcondSet (funOf u (ofNat 0)) (ofNat 0) (ofNat 1) := by
  rw [app, funOf.dcondSet, PairSeq.app_zero, PairSeq.app_zero]

theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (plusR a b) := by
  constructor
  change plusR a b =
    graph (fun u => funOf (plusR a b) (funOf (plusR a b) u))
  apply graph_ext
  intro u
  rw [app a b u]
  rcases dcondSet.cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, app,
      PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_zero, retract_app ha]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, app,
      PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_one, retract_app hb]
  · rw [dcondSet.of_mixed h.1 h.2, top]
  · rw [dcondSet.of_empty h.1 h.2, bot]

theorem isStrict (a b : Pomega) : IsStrict (plusR a b) :=
  bot a b

theorem typed_bot (a b : Pomega) : typed botElem (plusR a b) := by
  rw [typed, app, funOf.bot, dcondSet.bot]

theorem typed_inl {a b x : Pomega} (hx : typed x a) :
    typed (pairSeq (ofNat 0) x) (plusR a b) := by
  rw [typed, app, PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_zero,
    ← hx]

theorem typed_inr {a b y : Pomega} (hy : typed y b) :
    typed (pairSeq (ofNat 1) y) (plusR a b) := by
  rw [typed, app, PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_one,
    ← hy]

theorem typed_top (a b : Pomega) : typed topElem (plusR a b) :=
  (top a b).symm

theorem typed_iff {a b u : Pomega} (ha : Retract a) (hb : Retract b) :
    typed u (plusR a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
          (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b) := by
  constructor
  · intro hu
    have hu' : u =
        dcondSet (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
          (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) := by
      simpa [typed, app] using hu
    rcases dcondSet.cases (funOf u (ofNat 0)) with h | h | h | h
    · refine Or.inr (Or.inr (Or.inl ⟨funOf a (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet.of_zero_not_pos h.1 h.2)
      · exact (retract_app ha (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inr (Or.inr ⟨funOf b (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet.of_pos_not_zero h.1 h.2)
      · exact (retract_app hb (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inl ?_)
      exact hu'.trans (dcondSet.of_mixed h.1 h.2)
    · refine Or.inl ?_
      exact hu'.trans (dcondSet.of_empty h.1 h.2)
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact typed_bot a b
    · rw [hu]; exact typed_top a b
    · rw [hx]; exact typed_inl hxt
    · rw [hy]; exact typed_inr hyt

end plusR

end DomainTheory.DataTypesAsLattices
