
module

public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem seq4_comp_isScottContinuous
    {f g h i : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun u => seq4 (f u) (g u) (h u) (i u)) :=
  graph_const_isScottContinuous
    (fun u z =>
      condSet z (f u)
        (condSet (predSet z) (g u)
          (condSet (predSet (predSet z)) (h u)
            (condSet (predSet (predSet (predSet z))) (i u) botElem))))
    (fun z =>
      continuous_nary
        (fun y t => condSet.isScottContinuous_left y t)
        (fun x t => condSet.isScottContinuous_mid x t)
        (fun x y => condSet.isScottContinuous_right x y)
        (const_isScottContinuous z) hf
        (continuous_nary
          (fun y t => condSet.isScottContinuous_left y t)
          (fun x t => condSet.isScottContinuous_mid x t)
          (fun x y => condSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet z)) hg
          (continuous_nary
            (fun y t => condSet.isScottContinuous_left y t)
            (fun x t => condSet.isScottContinuous_mid x t)
            (fun x y => condSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet z))) hh
            (continuous_nary
              (fun y t => condSet.isScottContinuous_left y t)
              (fun x t => condSet.isScottContinuous_mid x t)
              (fun x y => condSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet (predSet (predSet z))))
              hi (const_isScottContinuous botElem)))))

end DomainTheory.DataTypesAsLattices
