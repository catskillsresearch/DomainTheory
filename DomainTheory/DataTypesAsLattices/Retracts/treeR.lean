/-ai
The tree retract is the application of the Y combinator to the graph of the tree functor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def treeR : Pomega := funOf Ycomb (graph treeF)

end DomainTheory.DataTypesAsLattices
