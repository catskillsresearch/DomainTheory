module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def termShift (u : Pomega) : Pomega :=
  graph (fun t => funOf u (succSet t))

namespace termShift

theorem isScottContinuous (u : Pomega) :
    IsScottContinuous (fun t => funOf u (succSet t)) :=
  theorem_1_3 (funOf.isScottContinuous u) succSet.isScottContinuous

theorem app (u t : Pomega) :
    funOf (termShift u) t = funOf u (succSet t) :=
  _root_.DomainTheory.DataTypesAsLattices.beta (termShift.isScottContinuous u) t

theorem left_isScottContinuous : IsScottContinuous termShift :=
  graph_const_isScottContinuous (fun u t => funOf u (succSet t))
    (fun t => funOf.isScottContinuous_left (succSet t))

theorem ofNat (u : Pomega) (i : ℕ) :
    funOf (termShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [termShift.app, succSet.ofNat]

end termShift

end DomainTheory.DataTypesAsLattices
