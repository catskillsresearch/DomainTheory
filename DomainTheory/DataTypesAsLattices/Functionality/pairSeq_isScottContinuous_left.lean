/-ai
For a fixed right argument, sequence pairing is Scott continuous in the left argument.

The graph of a family continuous in a parameter is Scott continuous in that parameter. For each test, the body is continuous in the left argument because a conditional set is continuous in its zero branch.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairSeq_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet_isScottContinuous_mid z _)

end DomainTheory.DataTypesAsLattices
