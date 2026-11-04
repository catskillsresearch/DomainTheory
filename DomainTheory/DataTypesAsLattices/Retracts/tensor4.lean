module

public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def tensor4 (a b c d : Pomega) : Pomega :=
  graph (fun u =>
    seq4 (funOf a (funOf u (ofNat 0)))
      (funOf b (funOf u (ofNat 1)))
      (funOf c (funOf u (ofNat 2)))
      (funOf d (funOf u (ofNat 3))))

namespace tensor4

theorem map_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun u =>
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3)))) :=
  seq4.comp_isScottContinuous
    (theorem_1_3 (funOf.isScottContinuous a) (funOf.isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf.isScottContinuous b) (funOf.isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf.isScottContinuous c) (funOf.isScottContinuous_left (ofNat 2)))
    (theorem_1_3 (funOf.isScottContinuous d) (funOf.isScottContinuous_left (ofNat 3)))

theorem app (a b c d u : Pomega) :
    funOf (tensor4 a b c d) u =
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3))) :=
  beta (map_isScottContinuous a b c d) u

theorem diag_isScottContinuous :
    IsScottContinuous (fun z => tensor4 z z z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      seq4 (funOf z (funOf u (ofNat 0)))
        (funOf z (funOf u (ofNat 1)))
        (funOf z (funOf u (ofNat 2)))
        (funOf z (funOf u (ofNat 3))))
    (fun u =>
      seq4.comp_isScottContinuous
        (funOf.isScottContinuous_left (funOf u (ofNat 0)))
        (funOf.isScottContinuous_left (funOf u (ofNat 1)))
        (funOf.isScottContinuous_left (funOf u (ofNat 2)))
        (funOf.isScottContinuous_left (funOf u (ofNat 3))))

theorem isRetract {a b c d : Pomega}
    (ha : Retract a) (hb : Retract b) (hc : Retract c) (hd : Retract d) :
    Retract (tensor4 a b c d) := by
  constructor
  change tensor4 a b c d =
    graph (fun u => funOf (tensor4 a b c d) (funOf (tensor4 a b c d) u))
  apply graph_ext
  intro u
  rw [app, app, seq4.zero, seq4.one, seq4.two, seq4.three,
    retract_app ha, retract_app hb, retract_app hc, retract_app hd]

end tensor4

end DomainTheory.DataTypesAsLattices
