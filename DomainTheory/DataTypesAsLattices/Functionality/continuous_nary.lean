module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_on_diag
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem continuous_nary {F : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => F x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => F x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => F x y z))
    {g h i : Pomega → Pomega}
    (hg : IsScottContinuous g) (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun x => F (g x) (h x) (i x)) :=
  continuous_on_diag
    (fun v => continuous_tuple (fun y => hf0 y (i v)) (fun x => hf1 x (i v)) hg hh)
    (fun u => theorem_1_3 (hf2 (g u) (h u)) hi)

end DomainTheory.DataTypesAsLattices
