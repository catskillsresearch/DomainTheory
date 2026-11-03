module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_5 (a b : Pomega) :
    dcondSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      Retract botElem :=
  ⟨dcondSet.bot _ _, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
