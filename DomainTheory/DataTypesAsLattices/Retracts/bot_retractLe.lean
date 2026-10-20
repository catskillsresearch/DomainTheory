module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_botElem
public import DomainTheory.DataTypesAsLattices.Retracts.graph_const_bot
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- The strict bottom retract is below every strict retract in Scott's
projection order. -/
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
