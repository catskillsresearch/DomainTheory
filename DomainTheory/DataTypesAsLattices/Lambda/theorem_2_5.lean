module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb.app]
  exact omega_first_recursion hf

end DomainTheory.DataTypesAsLattices
