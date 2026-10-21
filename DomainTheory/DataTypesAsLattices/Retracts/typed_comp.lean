/-ai
The composite of a map typed by the function space from a retract a to a retract b with a map typed by the function space from b to a set c is typed by the function space from a to c. The retract hypothesis on c is not used.

Both typing equations write the maps as the corresponding double composites. Rewrite the desired equation by the function-space application law and compare graphs. At each argument, the first typing equation writes the value of the first map as b applied after that map applied after a, the restriction equation removes the inner application of a, the second typing equation writes the value of the second map as c applied after that map applied after b, and the range equation removes that application of b.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.typed_arrowR_restrict
public import DomainTheory.DataTypesAsLattices.Retracts.typed_arrowR_range

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_comp {a b c f f' : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (_hc : IsRetract c)
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR b c)) :
    typed (comp f' f) (arrowR a c) := by
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  change comp f' f = funOf (arrowR a c) (comp f' f)
  rw [arrowR_app]
  apply graph_ext
  intro x
  have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
    simpa [comp_app] using congrArg (fun w => funOf w x) hf1
  have hrest := typed_arrowR_restrict ha hf
  have hfa : funOf f (funOf a x) = funOf f x := by
    simpa [comp_app] using (congrArg (fun w => funOf w x) hrest).symm
  have hf'fx : funOf f' (funOf f x) =
      funOf c (funOf f' (funOf b (funOf f x))) := by
    simpa [comp_app] using congrArg (fun w => funOf w (funOf f x)) hf2
  have hrange := typed_arrowR_range hb hf
  have hbval : funOf b (funOf f (funOf a x)) = funOf f (funOf a x) := by
    simpa [comp_app] using (congrArg (fun w => funOf w (funOf a x)) hrange).symm
  simp only [comp_app]
  rw [hf'fx, ← hfa, hbval, hfa]

end DomainTheory.DataTypesAsLattices
