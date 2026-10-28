module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_4.ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2.zero x y, seq2.one x y⟩

theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      Retract botElem :=
  ⟨fun x y => theorem_4_4.ii x y, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
