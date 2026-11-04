module

public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.ContinuityHelpers
public import DomainTheory.DataTypesAsLattices.Functionality.PairSeq
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

namespace tensorR

theorem map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1)))) :=
  ContinuityHelpers.tuple
    (fun y => PairSeq.isScottContinuous_left y)
    (fun x => PairSeq.isScottContinuous_right x)
    (theorem_1_3 (funOf.isScottContinuous a) (funOf.isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf.isScottContinuous b) (funOf.isScottContinuous_left (ofNat 1)))

theorem right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => tensorR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
    (fun u =>
      theorem_1_3
        (f := fun y => pairSeq (funOf a (funOf u (ofNat 0))) y)
        (g := fun b => funOf b (funOf u (ofNat 1)))
        (PairSeq.isScottContinuous_right (funOf a (funOf u (ofNat 0))))
        (funOf.isScottContinuous_left (funOf u (ofNat 1))))

theorem app (a b u : Pomega) :
    funOf (tensorR a b) u =
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))) :=
  beta (map_isScottContinuous a b) u

theorem diag_isScottContinuous :
    IsScottContinuous (fun z => tensorR z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      pairSeq (funOf z (funOf u (ofNat 0))) (funOf z (funOf u (ofNat 1))))
    (fun u =>
      ContinuityHelpers.tuple
        (fun y => PairSeq.isScottContinuous_left y)
        (fun x => PairSeq.isScottContinuous_right x)
        (funOf.isScottContinuous_left (funOf u (ofNat 0)))
        (funOf.isScottContinuous_left (funOf u (ofNat 1))))

theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (tensorR a b) := by
  constructor
  change tensorR a b =
    graph (fun u => funOf (tensorR a b) (funOf (tensorR a b) u))
  apply graph_ext
  intro u
  rw [app, app, PairSeq.app_zero, PairSeq.app_one, retract_app ha, retract_app hb]

end tensorR

end DomainTheory.DataTypesAsLattices
