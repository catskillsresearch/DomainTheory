
module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_isGraph {a b f : Pomega} (hf : typed f (arrowR a b)) :
    f = graph (fun x => funOf f x) := by
  have hf' := arrowR.typed_of hf
  apply Eq.trans hf'
  apply graph_ext
  intro x
  have : funOf f x = funOf b (funOf f (funOf a x)) := by
    have h1 : funOf f x = funOf (comp b (comp f a)) x :=
      congrArg (fun w => funOf w x) hf'
    rw [h1, comp.app, comp.app]
  rw [comp.app, this]

end DomainTheory.DataTypesAsLattices
