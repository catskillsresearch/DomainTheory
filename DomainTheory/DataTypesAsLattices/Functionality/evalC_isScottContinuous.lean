module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem evalC_isScottContinuous :
    IsScottContinuous (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => funOf.isScottContinuous_left y)
    (fun t => funOf.isScottContinuous t)
    (funOf.isScottContinuous_left (ofNat 0))
    (funOf.isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
