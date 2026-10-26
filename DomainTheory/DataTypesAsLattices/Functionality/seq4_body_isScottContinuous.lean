
module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq4_body_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun z =>
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem)))) :=
  continuous_nary
    (fun y t => condSet.isScottContinuous_left y t)
    (fun x t => condSet.isScottContinuous_mid x t)
    (fun x y => condSet.isScottContinuous_right x y)
    id_isScottContinuous (const_isScottContinuous a)
    (continuous_nary
      (fun y t => condSet.isScottContinuous_left y t)
      (fun x t => condSet.isScottContinuous_mid x t)
      (fun x y => condSet.isScottContinuous_right x y)
      predSet.isScottContinuous (const_isScottContinuous b)
      (continuous_nary
        (fun y t => condSet.isScottContinuous_left y t)
        (fun x t => condSet.isScottContinuous_mid x t)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (f := predSet) (g := predSet)
          predSet.isScottContinuous predSet.isScottContinuous)
        (const_isScottContinuous c)
        (continuous_nary
          (fun y t => condSet.isScottContinuous_left y t)
          (fun x t => condSet.isScottContinuous_mid x t)
          (fun x y => condSet.isScottContinuous_right x y)
          (theorem_1_3 (f := predSet)
            (g := fun z => predSet (predSet z))
            predSet.isScottContinuous
            (theorem_1_3 (f := predSet) (g := predSet)
              predSet.isScottContinuous predSet.isScottContinuous))
          (const_isScottContinuous d) (const_isScottContinuous botElem))))

end DomainTheory.DataTypesAsLattices
