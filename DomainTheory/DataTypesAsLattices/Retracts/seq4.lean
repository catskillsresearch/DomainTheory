module

public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.PlotkinHelpers
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.ContinuityHelpers
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def seq4 (a b c d : Pomega) : Pomega :=
  graph (fun z =>
    condSet z a
      (condSet (predSet z) b
        (condSet (predSet (predSet z)) c
          (condSet (predSet (predSet (predSet z))) d botElem))))

namespace seq4

theorem body_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun z =>
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem)))) :=
  ContinuityHelpers.nary
    (fun y t => condSet.isScottContinuous_left y t)
    (fun x t => condSet.isScottContinuous_mid x t)
    (fun x y => condSet.isScottContinuous_right x y)
    id_isScottContinuous (const_isScottContinuous a)
    (ContinuityHelpers.nary
      (fun y t => condSet.isScottContinuous_left y t)
      (fun x t => condSet.isScottContinuous_mid x t)
      (fun x y => condSet.isScottContinuous_right x y)
      predSet.isScottContinuous (const_isScottContinuous b)
      (ContinuityHelpers.nary
        (fun y t => condSet.isScottContinuous_left y t)
        (fun x t => condSet.isScottContinuous_mid x t)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (f := predSet) (g := predSet)
          predSet.isScottContinuous predSet.isScottContinuous)
        (const_isScottContinuous c)
        (ContinuityHelpers.nary
          (fun y t => condSet.isScottContinuous_left y t)
          (fun x t => condSet.isScottContinuous_mid x t)
          (fun x y => condSet.isScottContinuous_right x y)
          (theorem_1_3 (f := predSet)
            (g := fun z => predSet (predSet z))
            predSet.isScottContinuous
            (theorem_1_3 (f := predSet) (g := predSet)
              predSet.isScottContinuous predSet.isScottContinuous))
          (const_isScottContinuous d) (const_isScottContinuous botElem))))

theorem comp_isScottContinuous
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
      ContinuityHelpers.nary
        (fun y t => condSet.isScottContinuous_left y t)
        (fun x t => condSet.isScottContinuous_mid x t)
        (fun x y => condSet.isScottContinuous_right x y)
        (const_isScottContinuous z) hf
        (ContinuityHelpers.nary
          (fun y t => condSet.isScottContinuous_left y t)
          (fun x t => condSet.isScottContinuous_mid x t)
          (fun x y => condSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet z)) hg
          (ContinuityHelpers.nary
            (fun y t => condSet.isScottContinuous_left y t)
            (fun x t => condSet.isScottContinuous_mid x t)
            (fun x y => condSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet z))) hh
            (ContinuityHelpers.nary
              (fun y t => condSet.isScottContinuous_left y t)
              (fun x t => condSet.isScottContinuous_mid x t)
              (fun x y => condSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet (predSet (predSet z))))
              hi (const_isScottContinuous botElem)))))

theorem app (a b c d z : Pomega) :
    funOf (seq4 a b c d) z =
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))) :=
  beta (body_isScottContinuous a b c d) z

theorem zero (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 0) = a := by
  rw [app, condSet.ofNat_zero]

theorem one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [app, condSet.ofNat_one, predSet.ofNat_succ, condSet.ofNat_zero]

theorem two (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 2) = c := by
  rw [app, condSet.ofNat_succ, predSet.ofNat_succ, condSet.ofNat_one,
    predSet.ofNat_succ, condSet.ofNat_zero]

theorem three (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 3) = d := by
  rw [app, condSet.ofNat_succ, predSet.ofNat_succ, condSet.ofNat_succ,
    predSet.ofNat_succ, condSet.ofNat_one, PlotkinHelpers.predSet_iterate_self,
    condSet.ofNat_zero]

end seq4

end DomainTheory.DataTypesAsLattices
