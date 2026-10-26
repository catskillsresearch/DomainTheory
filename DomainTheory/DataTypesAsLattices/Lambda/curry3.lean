module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def curry3 (f : Pomega → Pomega → Pomega → Pomega)
    (_hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (_hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (_hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => f x y z)))

end DomainTheory.DataTypesAsLattices
