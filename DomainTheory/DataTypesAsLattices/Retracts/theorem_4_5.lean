module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_5.strict (a b : Pomega) :
    dcondSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem :=
  dcondSet.bot _ _

theorem theorem_4_5 :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      Retract botElem :=
  ⟨theorem_4_5.strict a b, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
