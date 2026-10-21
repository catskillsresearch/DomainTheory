/-ai
If f is typed by the function retract from a to b, then f equals the graph of its own application.

The arrow typing supplies an equality. Transitivity and extensionality of graphs reduce the claim to a pointwise identity. Congruence of application along that equality writes the application of f as the application of the composite of b with the composite of f and a. Two composition laws unfold that composite to b applied to f applied to a applied to the argument, and one further composition law matches this expression.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem typed_isGraph {a b f : Pomega} (hf : typed f (arrowR a b)) :
    f = graph (fun x => funOf f x) := by
  have hf' := typed_of_arrowR hf
  apply Eq.trans hf'
  apply graph_ext
  intro x
  have : funOf f x = funOf b (funOf f (funOf a x)) := by
    have h1 : funOf f x = funOf (comp b (comp f a)) x :=
      congrArg (fun w => funOf w x) hf'
    rw [h1, comp_app, comp_app]
  rw [comp_app, this]

end DomainTheory.DataTypesAsLattices
