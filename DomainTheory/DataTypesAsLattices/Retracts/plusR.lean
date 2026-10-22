module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.10), modified.** The displayed equation writes the
ordinary McCarthy conditional `⊃`. Lean uses the doubly strict
conditional `⊐` of (4.4), as in `bool` (4.3), which (4.8)–(4.10)
generalize. Mixed tags therefore map to `⊤` rather than the union of
the two injections; that is required for `⊕` to be a retract
(Theorem 4.5). This is not a symbol-for-symbol transcription of the
displayed (4.10). -/
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
