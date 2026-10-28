module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_more
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))

namespace boxTensor

theorem app (a b u : Pomega) :
    funOf (boxTensor a b) u =
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) :=
  beta (theorem_1_3.tuple
    (f := fun x y => squarePair (funOf a x) (funOf b y))
    (fun y => theorem_1_3 (f := fun x => squarePair x (funOf b y)) (g := funOf a)
      (squarePair.isScottContinuous_left (funOf b y))
      (funOf.isScottContinuous a))
    (fun x => theorem_1_3 (f := fun y => squarePair (funOf a x) y) (g := funOf b)
      (squarePair.isScottContinuous_right (funOf a x))
      (funOf.isScottContinuous b))
    squareFst.isScottContinuous squareSnd.isScottContinuous) u

theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (boxTensor a b) := by
  constructor
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor.app, boxTensor.app, _root_.DomainTheory.DataTypesAsLattices.eq_5_9,
    _root_.DomainTheory.DataTypesAsLattices.eq_5_10, retract_app ha, retract_app hb]

end boxTensor

end DomainTheory.DataTypesAsLattices
