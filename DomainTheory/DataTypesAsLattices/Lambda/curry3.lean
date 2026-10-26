module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices
def curry3 (f : Pomega → Pomega → Pomega → Pomega)
    (_hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (_hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (_hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => f x y z)))

namespace curry3

theorem app (f : Pomega → Pomega → Pomega → Pomega)
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) (x y z : Pomega) :
    funOf (funOf (funOf (curry3 f hf0 hf1 hf2) x) y) z = f x y z := by
  have h1 : funOf (curry3 f hf0 hf1 hf2) x =
      graph (fun y => graph (fun z => f x y z)) :=
    beta (graph_const_isScottContinuous
      (fun x y => graph (fun z => f x y z))
      (fun y => graph_const_isScottContinuous (fun x z => f x y z)
        (fun z => hf0 y z))) x
  have h2 : funOf (funOf (curry3 f hf0 hf1 hf2) x) y =
      graph (fun z => f x y z) := by
    rw [h1]
    exact beta (graph_const_isScottContinuous (fun y z => f x y z)
      (fun z => hf1 x z)) y
  rw [h2]
  exact beta (hf2 x y) z

end curry3

end DomainTheory.DataTypesAsLattices
