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
    (ha : Retract a) (hb : Retract b) (_hc : Retract c)
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
