module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.plus7Body

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Seven-way tagged sum with indices `0,...,6`, dispatching by iterated
predecessor on the tag so mixed tags collapse to `⊤` as in (4.4). -/
def plus7 (a0 a1 a2 a3 a4 a5 a6 : Pomega) : Pomega :=
  graph (plus7Body a0 a1 a2 a3 a4 a5 a6)

end DomainTheory.DataTypesAsLattices
