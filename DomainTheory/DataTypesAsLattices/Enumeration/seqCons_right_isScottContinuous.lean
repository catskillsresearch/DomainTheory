module

public import DomainTheory.DataTypesAsLattices.Lambda.seqCons
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem seqCons_right_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun xs => seqCons x xs) :=
  graph_const_isScottContinuous
    (fun xs z => condSet z x (funOf xs (predSet z)))
    (fun z => theorem_1_3 (condSet.isScottContinuous_right z x)
      (funOf.isScottContinuous_left (predSet z)))

end DomainTheory.DataTypesAsLattices
