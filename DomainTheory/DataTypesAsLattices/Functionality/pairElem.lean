module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Pairing of elements of `Pω` as a graph (Table 2 / (2.21)). -/
def pairElem (x y : Pomega) : Pomega := seq2 x y

namespace pairElem

theorem tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2.tag_ne x y

theorem eq_pairSeq (x y : Pomega) : pairElem x y = pairSeq x y := rfl

theorem fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2.zero x y

theorem snd (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y :=
  seq2.one x y

end pairElem

end DomainTheory.DataTypesAsLattices
