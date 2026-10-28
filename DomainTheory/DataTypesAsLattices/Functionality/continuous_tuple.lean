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

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem continuous_tuple {F : Pomega → Pomega → Pomega}
    (h1 : ∀ y, IsScottContinuous (fun x => F x y))
    (h2 : ∀ x, IsScottContinuous (fun y => F x y))
    {g h : Pomega → Pomega} (hg : IsScottContinuous g) (hh : IsScottContinuous h) :
    IsScottContinuous (fun x => F (g x) (h x)) :=
  continuous_on_diag
    (fun v => theorem_1_3 (h1 (h v)) hg)
    (fun u => theorem_1_3 (h2 (g u)) hh)

end DomainTheory.DataTypesAsLattices
