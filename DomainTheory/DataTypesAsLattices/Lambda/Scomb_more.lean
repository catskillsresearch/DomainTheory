module

public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Scomb

theorem inner_cont (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  theorem_1_3.tuple
    (fun y => funOf.isScottContinuous_left y)
    (fun t => funOf.isScottContinuous t)
    (funOf.isScottContinuous u)
    (funOf.isScottContinuous v)

theorem map_cont :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v => graph_const_isScottContinuous
      (fun u x => funOf (funOf u x) (funOf v x))
      (fun x => theorem_1_3
        (f := fun t => funOf t (funOf v x))
        (g := fun u => funOf u x)
        (funOf.isScottContinuous_left (funOf v x))
        (funOf.isScottContinuous_left x)))

theorem mid_cont (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x => theorem_1_3 (funOf.isScottContinuous (funOf u x))
      (funOf.isScottContinuous_left x))

theorem beta (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  _root_.DomainTheory.DataTypesAsLattices.beta Scomb.map_cont f

theorem beta2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb.beta]
  exact _root_.DomainTheory.DataTypesAsLattices.beta (Scomb.mid_cont f) g

theorem beta3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb.beta2]
  exact _root_.DomainTheory.DataTypesAsLattices.beta (Scomb.inner_cont f g) x

theorem isGraph : Scomb = graph (fun u => funOf Scomb u) := by
  apply graph_ext
  intro u
  rw [Scomb.beta]

theorem app_isGraph (f : Pomega) :
    funOf Scomb f = graph (fun g => funOf (funOf Scomb f) g) := by
  rw [Scomb.beta]
  apply graph_ext
  intro g
  exact (_root_.DomainTheory.DataTypesAsLattices.beta (Scomb.mid_cont f) g).symm

theorem app2_isGraph (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf (funOf Scomb f) g) x) := by
  rw [Scomb.beta2]
  apply graph_ext
  intro x
  exact (_root_.DomainTheory.DataTypesAsLattices.beta (Scomb.inner_cont f g) x).symm

end Scomb

end DomainTheory.DataTypesAsLattices
