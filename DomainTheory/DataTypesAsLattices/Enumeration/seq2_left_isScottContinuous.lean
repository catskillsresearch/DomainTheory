module

public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.predSet

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem seq2_left_isScottContinuous (b : Pomega) :
    IsScottContinuous (fun a => seq2 a b) :=
  graph_const_isScottContinuous
    (fun a z => condSet z a (condSet (predSet z) b botElem))
    (fun z => condSet.isScottContinuous_mid z _)

end DomainTheory.DataTypesAsLattices
