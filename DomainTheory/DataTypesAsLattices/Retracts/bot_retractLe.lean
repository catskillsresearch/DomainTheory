module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_botElem
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem bot_retractLe {a : Pomega} (ha : IsStrict a) :
    retractLe botElem a := by
  constructor
  · unfold comp
    have h : (fun x => funOf botElem (funOf a x)) = fun _ => botElem := by
      funext x
      exact funOf_botElem (funOf a x)
    rw [h, graph_const_bot]
  · unfold comp
    have h : (fun x => funOf a (funOf botElem x)) = fun _ => botElem := by
      funext x
      rw [funOf_botElem, ha]
    rw [h, graph_const_bot]

end DomainTheory.DataTypesAsLattices
