module

public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.interStep
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def interC : Pomega := fix interStep

namespace interC

theorem else_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x =>
      succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  refine theorem_1_3 (f := succSet) (g := fun x =>
      funOf (funOf interC (predSet x)) (predSet y))
    succSet.isScottContinuous ?_
  refine theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun x => funOf interC (predSet x))
    (funOf.isScottContinuous_left (predSet y)) ?_
  exact theorem_1_3 (funOf.isScottContinuous interC) predSet.isScottContinuous

theorem then_else_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y)))) :=
  theorem_1_3.tuple
    (fun els => condSet.isScottContinuous_mid x els)
    (fun th => condSet.isScottContinuous_right x th)
    (condSet.isScottContinuous_left (ofNat 0) botElem)
    (theorem_1_3 succSet.isScottContinuous
      (theorem_1_3 (funOf.isScottContinuous (funOf interC (predSet x)))
        predSet.isScottContinuous))

theorem body_isScottContinuous :
    IsScottContinuous (fun x =>
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y))))) :=
  graph_const_isScottContinuous
    (fun x y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))))
    (fun y =>
      theorem_1_3.tuple
        (fun els => condSet.isScottContinuous_left
          (condSet y (ofNat 0) botElem) els)
        (fun tes => condSet.isScottContinuous_right tes
          (condSet y (ofNat 0) botElem))
        id_isScottContinuous
        (interC.else_isScottContinuous y))

theorem unfold : interC = interStep interC :=
  (theorem_1_4 interStep.isScottContinuous).1.symm

theorem app_graph (x : Pomega) :
    funOf interC x =
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y)))) := by
  nth_rw 1 [interC.unfold]
  exact _root_.DomainTheory.DataTypesAsLattices.beta interC.body_isScottContinuous x

theorem app (x y : Pomega) :
    funOf (funOf interC x) y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  rw [interC.app_graph]
  exact _root_.DomainTheory.DataTypesAsLattices.beta (interC.then_else_isScottContinuous x) y

end interC

end DomainTheory.DataTypesAsLattices
