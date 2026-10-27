module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.HF

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem HF_isScottContinuous : IsScottContinuous HF :=
  graph_const_isScottContinuous
    (fun H e => graph (fun t => Hstep H e t))
    (fun e => graph_const_isScottContinuous (fun H t => Hstep H e t)
      (fun t => Hstep.isScottContinuous_H e t))

end DomainTheory.DataTypesAsLattices
