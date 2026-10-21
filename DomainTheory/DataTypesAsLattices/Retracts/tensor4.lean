/-ai
Scott 1976, before (4.44). The four-fold product by expanded indices is the graph of the map that applies the four retracts to the zeroth through third components of the argument and packs the four values as a four-place sequence. The construction uses those expanded indices for the product.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.seq4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, before (4.44).** Four-fold product by expanded indices,
not iterated binary `⊗`. -/
def tensor4 (a b c d : Pomega) : Pomega :=
  graph (fun u =>
    seq4 (funOf a (funOf u (ofNat 0)))
      (funOf b (funOf u (ofNat 1)))
      (funOf c (funOf u (ofNat 2)))
      (funOf d (funOf u (ofNat 3))))

end DomainTheory.DataTypesAsLattices
