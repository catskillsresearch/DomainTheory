module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def vaalF (v : Pomega) : Pomega :=
  graph (fun x =>
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))

namespace vaalF

theorem body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))) :=
  continuous_nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (const_isScottContinuous Gcomb)
    (continuous_tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun u => funOf.isScottContinuous u)
      (theorem_1_3 (funOf.isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 0))
          (g := fun x => funOf x (ofNat 1))
          (funOf.isScottContinuous_left (ofNat 0))
          (funOf.isScottContinuous_left (ofNat 1))))
      (theorem_1_3 (funOf.isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 1))
          (g := fun x => funOf x (ofNat 1))
          (funOf.isScottContinuous_left (ofNat 1))
          (funOf.isScottContinuous_left (ofNat 1)))))

theorem app (v x : Pomega) :
    funOf (vaalF v) x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))) :=
  beta (vaalF.body_isScottContinuous v) x

theorem isScottContinuous : IsScottContinuous vaalF :=
  graph_const_isScottContinuous
    (fun v x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))
    (fun x =>
      theorem_1_3
        (condSet.isScottContinuous_right (funOf x (ofNat 0)) Gcomb)
        (continuous_tuple
          (fun y => funOf.isScottContinuous_left y)
          (fun u => funOf.isScottContinuous u)
          (funOf.isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf.isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 1)))))

end vaalF

end DomainTheory.DataTypesAsLattices
